/**
 * Copyright (c) 2014 MIT License by 6.172 Staff
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 **/

/*

The search module contains the alpha-beta search utilities for Leiserchess,
consisting of three main functions:

  1. searchRoot() is called from outside the module.
  2. scout_search() performs a null-window search.  There are two versions
     of this function in search_ref.c and search_mod.c.  The former is for
     reference, so that when you build with TEST enabled, the modified
     version's results can be compared for correctness.
  3. searchPV() performs the normal alpha-beta search.

searchRoot() calls scout_search() to order the moves.  searchRoot() then
calls searchPV() to perform the full search.  A sample parallel
implementation has been provided for you.

 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <ctype.h>
#include <stdbool.h>
#include <string.h>

#define __STDC_FORMAT_MACROS
#include <inttypes.h>

#include "eval.h"
#include "search.h"
#include "tt.h"
#include "util.h"
#include "fen.h"
#include "tbassert.h"

#include <pthread.h>
#include <cilk/cilk.h>
#include <cilk/reducer.h>
#include "speculative_add.h"

// -----------------------------------------------------------------------------
// Preprocessor
// -----------------------------------------------------------------------------

#define ABORT_CHECK_PERIOD 0xfff

// -----------------------------------------------------------------------------
// READ ONLY settings (see iopt)
// -----------------------------------------------------------------------------

// value of a draw
int DRAW;

// POSITIONAL WEIGHTS evaluation terms
int HMB; // having the move bonus

// Late-move reduction
int LMR_R1;    // Look at this number of moves full width before reducing 1 ply
int LMR_R2;    // After this number of moves reduce 2 ply

int USE_NMM;
int TRACE_MOVES;   // Print moves
int DETECT_DRAWS;  // Detect draws by repetition

// do not set more than 5 ply
int FUT_DEPTH;     // set to zero for no futilty

// -----------------------------------------------------------------------------
// Sort related
// -----------------------------------------------------------------------------

typedef uint32_t sort_key_t;
static const uint64_t SORT_MASK = (1ULL << 32) - 1;
static const int SORT_SHIFT = 32;

sort_key_t sort_key(sortable_move_t mv) {
  return (sort_key_t) ((mv >> SORT_SHIFT) & SORT_MASK);
}

void set_sort_key(sortable_move_t *mv, sort_key_t key) {
  // sort keys must not exceed SORT_MASK
  //  assert ((0 <= key) && (key <= SORT_MASK));
  *mv = ((((uint64_t) key) & SORT_MASK) << SORT_SHIFT) |
        (*mv & ~(SORT_MASK << SORT_SHIFT));
  return;
}

// -----------------------------------------------------------------------------
// Time
// -----------------------------------------------------------------------------

#if !TEST // We should not be worrying about time if we are in test mode

// tic counter for how often we should check for abort
static int     tics = 0;
static double  sstart;    // start time of a search in milliseconds
static double  timeout;   // time elapsed before abort
static bool    abortf = false;  // abort flag for search

void init_abort_timer(double goal_time) {
  sstart = milliseconds();
  // don't go over any more than 3 times the goal
  timeout = sstart + goal_time * 3.0;
}

double elapsed_time() {
  return milliseconds() - sstart;
}

bool should_abort() {
  return abortf;
}

void reset_abort() {
  abortf = false;
}

void init_tics() {
  tics = 0;
}

#endif

// -----------------------------------------------------------------------------
// Heuristic tables
// -----------------------------------------------------------------------------

// note: these need to be tuned but this should be pretty conservative
//       probably we would only use 3 or 4 of these values at most
// score_t fmarg[10] = { 0,  50, 100, 250, 450, 700, 1000, 1500, 2000, 3000 };
static score_t fmarg[10] = {
  0, PAWN_VALUE / 2, PAWN_VALUE, (PAWN_VALUE * 5) / 2, (PAWN_VALUE * 9) / 2,
  PAWN_VALUE * 7, PAWN_VALUE * 10, PAWN_VALUE * 15, PAWN_VALUE * 20,
  PAWN_VALUE * 30
};

// -----------------------------------------------------------------------------
// Move helpers
// -----------------------------------------------------------------------------

move_t get_move(sortable_move_t sortable_mv) {
  return (move_t) (sortable_mv & MOVE_MASK);
}

// Detect move repetition
static bool is_repeated(position_t *p, score_t *score, int ply) {
  if (!DETECT_DRAWS) {
    return false;   // no draw detected
  }

  position_t *x = p->history;
  uint64_t cur = p->key;

  while (true) {
    if (!zero_victims(x->victims)) {
      break;  // cannot be a repetition
    }
    x = x->history;
    if (!zero_victims(x->victims)) {
      break;  // cannot be a repetition
    }
    if (x->key == cur) {               // is a repetition
      if (ply & 1) {
        *score = -DRAW;
      } else {
        *score = DRAW;
      }
      return true;
    }
    x = x->history;
  }
  return false;
}

// check the victim pieces returned by the move to determine if it's a
// game-over situation.  If so, also calculate the score depending on
// the pov (which player's point of view)
static bool is_game_over(victims_t victims, score_t *score, int pov, int ply) {
  tbassert(ptype_of(victims.stomped) != KING, "Stomped a king.\n");
  if (ptype_of(victims.zapped) == KING) {
    if (color_of(victims.zapped) == WHITE) {
      *score = -WIN * pov;
    } else {
      *score = WIN * pov;
    }
    if (*score < 0) {
      *score += ply;
    } else {
      *score -= ply;
    }
    return true;
  }
  return false;
}

// -----------------------------------------------------------------------------
// Print helpers
// -----------------------------------------------------------------------------

static void getPV(move_t *pv, char *buf) {
  buf[0] = 0;

  for (int i = 0; i < (MAX_PLY_IN_SEARCH - 1) && pv[i] != 0; i++) {
    char a[MAX_CHARS_IN_MOVE];
    move_to_str(pv[i], a);
    if (i != 0) {
      strcat(buf, " ");
    }
    strcat(buf, a);
  }
  return;
}

// Main search routines and helper functions
typedef enum searchType {  // different types of search
  SEARCH_PV,
  SEARCH_NON_PV,
} searchType_t;

static void print_move_info(move_t mv, int ply) {
  char buf[MAX_CHARS_IN_MOVE];
  move_to_str(mv, buf);
  printf("info");
  for (int i = 0; i < ply; ++i) {
    printf(" ----");
  }
  printf(" %s\n", buf);
}

// -----------------------------------------------------------------------------
// Search datastructures
// -----------------------------------------------------------------------------

//// Killer moves table and lookup function
//
#define __KMT_dim__ [MAX_PLY_IN_SEARCH][4]
#define KMT(ply,id) (4 * ply + id)
static move_t killer_reference __KMT_dim__; // up to 4 killers

//// Best move history table and lookup function
//
// Format: best_move_history[color_t][piece_t][square_t][orientation]
#define __BMH_dim__ [2][6][ARR_SIZE][NUM_ORI]
#define BMH(color,piece,square,ori) (color * 6 * ARR_SIZE * NUM_ORI + piece * ARR_SIZE * NUM_ORI + square * NUM_ORI + ori)
static int best_move_history_reference __BMH_dim__;

void init_best_move_history() {
  memset(best_move_history_reference, 0, sizeof(best_move_history_reference));
}

static void update_best_move_history( position_t *p, int index_of_best,
                                      sortable_move_t *lst, int count,
                                      int * best_move_history) {
  tbassert(ENABLE_TABLES, "Tables weren't enabled.\n");

  int color_to_move = color_to_move_of(p);

  for (int i = 0; i < count; i++) {
    move_t   mv  = get_move(lst[i]);
    ptype_t  pce = ptype_mv_of(mv);
    rot_t    ro  = rot_of(mv);   // rotation
    square_t fs  = from_square(mv);
    int      ot  = ORI_MASK & (ori_of(p->board[fs]) + ro);
    square_t ts  = to_square(mv);

    int  s = best_move_history[BMH(color_to_move,pce,ts,ot)];

    if (index_of_best == i) {
      s = s + 11200; // number will never exceed 1017
    }
    s = s * 0.90; // decay score over time

    tbassert(s < 102000, "s = %d\n", s); // or else sorting will fail

    best_move_history[BMH(color_to_move,pce,ts,ot)] = s;
  }
}

// -----------------------------------------------------------------------------
// Search Code
//
// This code has two versions: a reference and a modified version.  The ref
// version is for you to compare your implementation against to verify
// correctness, insofar as your code is deterministic.
// -----------------------------------------------------------------------------

#define subtree_scout subtree_scout_ref
#define scout_search scout_search_ref

#include "search_ref.c"

#undef subtree_scout
#undef scout_search

#define subtree_scout subtree_scout_mod
#define scout_search scout_search_mod

#define STUDENT_SEARCH 1
#include "search_mod.c"

#undef subtree_scout
#undef scout_search

#if RUN_REFERENCE_CODE == 0
// Run with the modified/student code.
#define scout_search scout_search_mod
#else
// Run with the reference code.
#define scout_search scout_search_ref
#endif

#if TEST

// -----------------------------------------------------------------------------
// Test framework assertions
// -----------------------------------------------------------------------------

// Copy data structures that both the reference / test codes use.  This is
// useful when you are comparing a serial test code to the reference code (i.e.,
// there is no non-determinism so it is OK that the tables are all enabled)
#define __MACRO_test_harness_setup \
      move_t killer_test __KMT_dim__; \
      int best_move_history_test __BMH_dim__; \
      memcpy(killer_test, killer_reference, sizeof(killer_reference)); \
      memcpy(best_move_history_test, best_move_history_reference, sizeof(best_move_history_reference)); \

// This code will check that your test code's scout search performs the same 
// beta cutoffs as the reference code
void test_harness(position_t * np, score_t alpha, int depth,
                  int ply, int reduction, move_t *pv, 
                  uint64_t * node_count_serial, Speculative_add * node_count_parallel,
                  move_t * killer, int * best_move_history,
                  Abort* parent_abort, int mv_index, 
                  score_t score_test) {
  char fen[MAX_FEN_CHARS];
  position_t np_test, np_conversion;

  // First, we will translate your board representation into the board 
  // representation that the reference code understands.  We use the FEN board 
  // representation as an intermediate representation to translate your board to 
  // the reference code board. (NOTE: pos_to_fen() and fen_to_pos() together 
  // perform an identity operation right now, since the reference code board 
  // representation == the test code board representation by default.
  // When/if you change your board representation, you will have to modify 
  // fen_to_pos().
  //
  // NOTE: you may also change the reference code to use your optimized board 
  // representation, but this may not catch as many bugs.  We recommend that you 
  // copy/paste the reference move_gen code so that the reference code ONLY 
  // touches the original board representation.  That way, all you have to do to 
  // run the tests is modify pos_to_fen.
  memcpy(&np_test, np, sizeof(position_t));
  pos_to_fen(np, fen);
  fen_to_pos(&np_conversion, fen);
  memcpy(&np_test.board, &np_conversion.board, sizeof(piece_t) * ARR_SIZE);

  score_t score_ref = -scout_search_ref(&np_test, -alpha, depth, ply, reduction, pv, 
                                              node_count_serial, node_count_parallel,
                                              killer, best_move_history, parent_abort);

  // if the ref / test codes don't result in the same beta-cutoff, the test code 
  // must be buggy!
  int cuttoff_condition = (score_ref > alpha) == (score_test > alpha);
  tbassert(cuttoff_condition, "Beta-cutoff MISMATCH! [expected = %d, actual = %d, alpha = %d, depth = %d, mv index = %d]\n", score_ref, score_test, alpha, depth, mv_index);
}

#endif // TEST

// -----------------------------------------------------------------------------
// searchPV
// 
// Search the principal variation of each board position
// -----------------------------------------------------------------------------

static
score_t searchPV(position_t *p, score_t alpha, score_t beta, int depth,
                 int ply, move_t *pv,
                 uint64_t * node_count_serial,
                 Speculative_add *node_count_parallel,
                 Abort *parent_abort) {
  pv[0] = 0;
  // get transposition table record if available
  ttRec_t *rec = tt_hashtable_get(p->key);
  int hash_table_move = 0;
  if (rec) {
    hash_table_move = tt_move_of(rec);
  }

  // init score
  score_t best_score = -INF;
  score_t sps = eval(p, false) + HMB;  // stand pat (having-the-move) bonus
  bool quiescence = (depth <= 0);      // are we in quiescence?
#if !TEST
  score_t orig_alpha = alpha;
#endif

  if (quiescence) {
    best_score = sps;
    if (best_score >= beta) {
      return best_score;
    }
    if (best_score > alpha) {
      alpha = best_score;
    }
  }

  position_t np;  // next position
  // generate move list
  sortable_move_t move_list[MAX_NUM_MOVES];
  int num_of_moves = generate_all(p, move_list, false); // number of moves in list

  int best_move_index = 0;   // index of best move found
  pthread_mutex_t local_mutex;
  pthread_mutex_init(&local_mutex, NULL);
  Abort child_abort;
  abort_constructor(&child_abort, parent_abort);

  color_t fake_color_to_move = color_to_move_of(p);
  int pov = 1 - fake_color_to_move * 2; // point of view = 1 for white, -1 for black
  move_t killer_a = killer_reference[ply][0];
  move_t killer_b = killer_reference[ply][1];

  int mv_index;

  // sort special moves to the front
  for (mv_index = 0; mv_index < num_of_moves; mv_index++) {
    move_t mv = get_move(move_list[mv_index]);
    if (mv == hash_table_move) {
      set_sort_key(&move_list[mv_index], SORT_MASK);
    } else if (mv == killer_a) {
      set_sort_key(&move_list[mv_index], SORT_MASK - 1);
    } else if (mv == killer_b) {
      set_sort_key(&move_list[mv_index], SORT_MASK - 2);
    } else {
      ptype_t  pce = ptype_mv_of(mv);
      rot_t    ro  = rot_of(mv);   // rotation
      square_t fs  = from_square(mv);
      int      ot  = ORI_MASK & (ori_of(p->board[fs]) + ro);
      square_t ts  = to_square(mv);
      set_sort_key(&move_list[mv_index], best_move_history_reference[fake_color_to_move][pce][ts][ot]);
    }
  }

  move_t subpv[MAX_PLY_IN_SEARCH];
  score_t score;

  int legal_move_count = 0;

  for (mv_index = 0; mv_index < num_of_moves; mv_index++) {
    subpv[0] = 0;

    // on the fly sorting
    for (int j = 0; j < num_of_moves; j++) {
      sortable_move_t insert = move_list[j];
      int hole = j;
      while (hole > 0 && insert > move_list[hole-1]) {
        move_list[hole] = move_list[hole-1];
        hole--;
      }
      move_list[hole] = insert;
    }

    move_t mv = get_move(move_list[mv_index]);
    if (TRACE_MOVES) {
      print_move_info(mv, ply);
    }

    int ext = 0;           // extensions
    bool blunder = false;  // shoot our own piece

#if PARALLEL
    spec_add(&REDUCER_VIEW(*node_count_parallel), 1);
#else
    (*node_count_serial)++;
#endif

    victims_t victims = make_move(p, &np, mv);  // make the move baby!
    if (is_KO(victims)) {
      continue;
    }

    if (is_game_over(victims, &score, pov, ply)) {
      goto scored;
    }

    if (zero_victims(victims) && quiescence) {
      continue;   // ignore noncapture moves in quiescence
    }
    tbassert(np.victims.stomped == 0
             || color_of(np.victims.stomped) != fake_color_to_move,
             "stomped = %d, color = %d, fake_color_to_move = %d\n",
             np.victims.stomped, color_of(np.victims.stomped),
             fake_color_to_move);
    if (np.victims.stomped == 0 && np.victims.zapped > 0 &&
	color_of(np.victims.zapped) == fake_color_to_move) {
      blunder = true;
    }
    if (quiescence && blunder) {
      continue;  // ignore own piece captures in quiescence
    }

    // A legal move is a move that's not KO, but when we are in quiescence
    // we only want to count moves that has a capture.
    legal_move_count++;
    if (victim_exists(victims) && !blunder) {
      ext = 1;  // extend captures
    }

    if (is_repeated(&np, &score, ply)) {
      goto scored;
    }

    // first move?
    if (legal_move_count == 1 || quiescence) {
      score = -searchPV(&np, -beta, -alpha, ext + depth - 1, ply + 1,
                        subpv, node_count_serial, node_count_parallel,
                        &child_abort);
#if TIMED_ABORTS
      if (abortf) {
        return 0;
      }
#endif
    } else {

#if TEST && defined(STUDENT_SEARCH)
      __MACRO_test_harness_setup
#endif

      score = -scout_search(  &np, -alpha, ext + depth - 1, ply + 1, 0, subpv, 
                              node_count_serial, node_count_parallel, 
                              &killer_reference[0][0], &best_move_history_reference[0][0][0][0],
                              &child_abort);

#if TEST && defined(STUDENT_SEARCH)
      test_harness( &np, alpha, ext + depth - 1, ply + 1, 0, subpv,
                    node_count_serial, node_count_parallel,
                    &killer_test[0][0], &best_move_history_test[0][0][0][0],
                    &child_abort, mv_index, 
                    score);
#endif

#if TIMED_ABORTS
      if (abortf) {
        return 0;
      }
#endif
      if (score > alpha) {
        score = -searchPV(&np, -beta, -alpha, ext + depth - 1, ply + 1,
                          subpv, node_count_serial, node_count_parallel,
                          &child_abort);
#if TIMED_ABORTS
        if (abortf) {
          return 0;
        }
#endif
      }

    }

   scored:
    if (score > best_score) {
      best_score = score;
      best_move_index = mv_index;
      pv[0] = mv;
      memcpy(pv+1, subpv, sizeof(move_t) * (MAX_PLY_IN_SEARCH - 1));
      pv[MAX_PLY_IN_SEARCH - 1] = 0;

      if (score > alpha) {
        alpha = score;
      }
      if (score >= beta) {
        if (mv != killer_reference[ply][0] && ENABLE_TABLES) {
          killer_reference[ply][1] = killer_reference[ply][0];
          killer_reference[ply][0] = mv;
        }
        break;
      }
    }
  }

  if (quiescence == false) {
    if (mv_index < num_of_moves) {
      mv_index++;   // moves tried
    }
    if (ENABLE_TABLES) update_best_move_history(p, best_move_index, move_list, mv_index, &best_move_history_reference[0][0][0][0]);
  }
  tbassert(abs(best_score) != -INF, "best_score = %d\n", best_score);

#if !TEST
  if (best_score <= orig_alpha) {
    tt_hashtable_put(p->key, depth,
        tt_adjust_score_for_hashtable(best_score, ply), UPPER, 0);
  } else if (best_score >= beta) {
    tt_hashtable_put(p->key, depth,
        tt_adjust_score_for_hashtable(best_score, ply), LOWER, pv[0]);
  } else {
    tt_hashtable_put(p->key, depth,
        tt_adjust_score_for_hashtable(best_score, ply), EXACT, pv[0]);
  }
#endif

  return best_score;
}

// -----------------------------------------------------------------------------
// searchRoot
//
// This handles scout search logic for the first level of the search tree
// -----------------------------------------------------------------------------

score_t searchRoot( position_t *p, score_t alpha, score_t beta, int depth,
                    int ply, move_t *pv, uint64_t *node_count_serial, Speculative_add *node_count_parallel, 
                    FILE *OUT, Abort *abort_p) {
  static int num_of_moves = 0; // number of moves in list
  // hopefully, more than we will need
  static sortable_move_t move_list[MAX_NUM_MOVES];

  if (depth == 1) {
    // we are at depth 1; generate all possible moves
    num_of_moves = generate_all(p, move_list, false);
    // shuffle the list of moves
    for (int i = 0; i < num_of_moves; i++) {
      int r = myrand() % num_of_moves;
      sortable_move_t tmp = move_list[i];
      move_list[i] = move_list[r];
      move_list[r] = tmp;
    }
  }

  score_t best_score = -INF;
  assert (best_score == alpha); // initial conditions
  move_t subpv[MAX_PLY_IN_SEARCH];
  color_t fake_color_to_move = color_to_move_of(p);
  int pov = 1 - fake_color_to_move * 2;  // pov = 1 for White, -1 for Black

  position_t np;           // next position
  score_t score;

  for (int mv_index = 0; mv_index < num_of_moves; mv_index++) {
    move_t mv = get_move(move_list[mv_index]);

    if (TRACE_MOVES) {
      print_move_info(mv, ply);
    }

#if PARALLEL
    spec_add(&REDUCER_VIEW(*node_count_parallel), 1);
#else
    (*node_count_serial)++;
#endif

    victims_t x = make_move(p, &np, mv);  // make the move baby!
    if (is_KO(x)) {
      continue;  // not a legal move
    }

    if (is_game_over(x, &score, pov, ply)) {
      subpv[0] = 0;
      goto scored;
    }

    if (is_repeated(&np, &score, ply)) {
      subpv[0] = 0;
      goto scored;
    }

    if (mv_index == 0 || depth == 1) {
      // We guess that the first move is the principle variation
      score = -searchPV(&np, -beta, -alpha, depth - 1, ply + 1,
                        subpv, node_count_serial, node_count_parallel, abort_p);
#if TIMED_ABORTS
      if (abortf) {
        return 0;
      }
#endif
    } else {

#if TEST
      __MACRO_test_harness_setup
#endif

      score = -scout_search(  &np, -alpha, depth - 1, ply + 1, 0,
                                      subpv, node_count_serial, node_count_parallel, 
                                      &killer_reference[0][0], &best_move_history_reference[0][0][0][0],
                                      abort_p);

#if TEST && RUN_REFERENCE_CODE == 0
      test_harness( &np, alpha, depth - 1, ply + 1, 0, subpv,
                    node_count_serial, node_count_parallel,
                    &killer_test[0][0], &best_move_history_test[0][0][0][0],
                    abort_p, mv_index,
                    score);
#endif

#if TIMED_ABORTS
      if (abortf) {
        return 0;
      }
#endif

      // If its score exceeds the current best score, 
      if (score > alpha) {
        score = -searchPV(&np, -beta, -alpha, depth - 1, ply + 1,
                          subpv, node_count_serial, node_count_parallel,
                          abort_p);
#if TIMED_ABORTS
        if (abortf) {
          return 0;
        }
#endif
      }
    }

  scored:
    // only valid for the root node:
    tbassert( (score > best_score) == (score > alpha),
              "score = %d, best = %d, alpha = %d\n", score, best_score, alpha);

    if (score > best_score) {
      tbassert(score > alpha, "score: %d, alpha: %d\n", score, alpha);

      best_score = score;
      pv[0] = mv;
      memcpy(pv+1, subpv, sizeof(move_t) * (MAX_PLY_IN_SEARCH - 1));
      pv[MAX_PLY_IN_SEARCH - 1] = 0;

      // Print out based on UCI (universal chess interface)
#if !TEST
      double et = elapsed_time();
#else
      double et = 0.0; // in test mode, time isn't really meaningful
#endif
      char   pvbuf[MAX_PLY_IN_SEARCH * MAX_CHARS_IN_MOVE];
      getPV(pv, pvbuf);
      if (et < 0.00001) {
        et = 0.00001; // hack so that we don't divide by 0
      }

#if PARALLEL
      uint64_t nps = 1000 * reducer_get_value(&REDUCER_VIEW(*node_count_parallel)) / et;

      fprintf(OUT, "info depth %d, move_no %d, score %d, time (microsec) %d, nodes %" PRIu64 
              ", nps %" PRIu64 "\n",
              depth, 0, best_score, (int) (et * 1000), reducer_get_value(&REDUCER_VIEW(*node_count_parallel)), nps);
#else
      uint64_t nps = 1000 * *node_count_serial / et;
      fprintf(OUT, "info depth %d move_no %d time (microsec) %d nodes %" PRIu64 
              " nps %" PRIu64 "\n",
              depth, mv_index + 1, (int) (et * 1000), *node_count_serial, nps);
#endif
      fprintf(OUT, "info score cp %d pv %s\n", score, pvbuf);

      // Slide this move to the front of the move list
      for (int j = mv_index; j > 0; j--) {
        move_list[j] = move_list[j - 1];
      }
      move_list[0] = mv;
    }

    // Normal alpha-beta logic: if the current score is better than what the 
    // maximizer has been able to get so far, take that new value.  Likewise, 
    // score >= beta is the beta cutoff condition
    if (score > alpha) {
      alpha = score; 
    }
    if (score >= beta) {
      tbassert(0, "score: %d, beta: %d\n", score, beta);
      break;
    }
  }

  return best_score;
}

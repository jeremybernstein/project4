/**
 * Copyright (c) 2012--2014 MIT License by 6.172 Staff
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

#include "tbassert.h"

// -----------------------------------------------------------------------------
// Scout Search
//
// This is the scout search implementation (and we have parallelized some 
// of it for you).
// -----------------------------------------------------------------------------

// We need a separate function so that we can cilk_spawn
void subtree_scout( int mv_index, sortable_move_t *move_list, int ply,
                    uint64_t * node_count_serial, Speculative_add *node_count, position_t *p, int depth,
                    score_t beta, Abort *abort, pthread_mutex_t *local_mutex,
                    score_t *best_score, int *best_move_index, move_t *pv, bool quiescence, 
                    position_t np, int ext, move_t mv, int next_reduction, 
                    move_t * killer, int * best_move_history);

static score_t scout_search(  position_t *p, score_t beta, int depth, int ply, int reduction, move_t *pv, 
                              uint64_t * node_count_serial, Speculative_add* node_count,
                              // optimization tables:
                              move_t * killer, int * best_move_history,
                              // Used only in parallel mode
                              Abort* parent_abort) {

  if (reduction > 0) {
    // We first perform a reduced depth search.
    int score = scout_search( p, beta, depth - reduction, ply, 0, pv, 
                              node_count_serial, node_count,
                              killer, best_move_history,
                              parent_abort);

    // -(parentBeta-1) = beta --> parentBeta = -beta+1
    int parentBeta = -beta + 1;
    int parentScore = -score;

    // No need to search to full depth, return this score.
    if (parentScore < parentBeta) {
      return score;
    }

 #if TIMED_ABORTS
    if (abortf) {
      return 0;
    }
#endif
  }

  pv[0] = 0;

  // check whether we should abort
#if PARALLEL
  Abort aborted;
  abort_constructor(&aborted, parent_abort);
  if (is_aborted(&aborted)) {
    return 0;
  }
#elif TIMED_ABORTS
  tics++;
  if ((tics & ABORT_CHECK_PERIOD) == 0) {
    if (milliseconds() >= timeout) {
      abortf = true;
      return 0;
    }
  }
#endif

  // get transposition table record if available
  int hash_table_move = 0;
  ttRec_t *rec = tt_hashtable_get(p->key);
  if (rec && !TEST) {
    if (tt_is_usable(rec, depth, beta)) {
      return tt_adjust_score_from_hashtable(rec, ply);
    }
    hash_table_move = tt_move_of(rec);
  }

  score_t best_score = -INF;
  score_t sps = eval(p, false) + HMB;  // stand pat (having-the-move) bonus
  bool quiescence = (depth <= 0);      // are we in quiescence?

  if (quiescence) {
    best_score = sps;
    if (best_score >= beta) {
      return best_score;
    }
  }

  // margin based forward pruning
  if (USE_NMM) {
    if (depth <= 2) {
      if (depth == 1 && sps >= beta + 3 * PAWN_VALUE) {
        return beta;
      }
      if (depth == 2 && sps >= beta + 5 * PAWN_VALUE) {
        return beta;
      }
    }
  }

  // futility pruning
  if (depth <= FUT_DEPTH && depth > 0) {
    if (sps + fmarg[depth] < beta) {
      // treat this ply as a quiescence ply, look only at captures
      quiescence = true;
      best_score = sps;
    }
  }

  position_t np;  // next position
  // hopefully, more than we will need
  sortable_move_t move_list[MAX_NUM_MOVES];
  // number of moves in list
  int num_of_moves = generate_all(p, move_list, false);

  color_t fake_color_to_move = color_to_move_of(p);
  int pov = 1 - fake_color_to_move * 2; // point of view = 1 for white, -1 for black
  move_t killer_a = killer[KMT(ply,0)];
  move_t killer_b = killer[KMT(ply,1)];

  // sort special moves to the front
  for (int mv_index = 0; mv_index < num_of_moves; mv_index++) {
    move_t mv = get_move(move_list[mv_index]);
    if (mv == hash_table_move) {
      tbassert(!TEST, "Test mode is on.\n");
      set_sort_key(&move_list[mv_index], SORT_MASK);
    } else if (mv == killer_a) {
      tbassert(ENABLE_TABLES, "ENABLE_TABLES is off.\n");
      set_sort_key(&move_list[mv_index], SORT_MASK - 1);
    } else if (mv == killer_b) {
      tbassert(ENABLE_TABLES, "ENABLE_TABLES is off.\n");
      set_sort_key(&move_list[mv_index], SORT_MASK - 2);
    } else {
      ptype_t  pce = ptype_mv_of(mv);
      rot_t    ro  = rot_of(mv);   // rotation
      square_t fs  = from_square(mv);
      int      ot  = ORI_MASK & (ori_of(p->board[fs]) + ro);
      square_t ts  = to_square(mv);
      set_sort_key(&move_list[mv_index], best_move_history[BMH(fake_color_to_move,pce,ts,ot)]);
    }
  }

  move_t subpv[MAX_PLY_IN_SEARCH];
  score_t score;

  int legal_move_count = 0;
  int mv_index;  // used outside of the loop
  int best_move_index = 0;   // index of best move found

#if PARALLEL
  pthread_mutex_t local_mutex;
  pthread_mutex_init(&local_mutex, NULL);
#endif

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

    // increase node count
    if (ENABLE_TABLES) {
      if (PARALLEL) {
        spec_add(&REDUCER_VIEW(*node_count), 1);
      } else {
        (*node_count_serial)++;
      }
    }

    victims_t victims = make_move(p, &np, mv);  // make the move baby!
    if (is_KO(victims)) {
      continue;
    }

    if (is_game_over(victims, &score, pov, ply)) {
      // Break out of loop.
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
      // Break out of loop.
      goto scored;
    }

    { // score the LMR so that compiler does not complain about next_reduction
      // initialized after goto statement
      // Late move reductions - or LMR
      int next_reduction = 0;
      if (legal_move_count >= LMR_R1 && depth > 2 &&
          zero_victims(victims) && mv != killer_a && mv != killer_b) {
        if (legal_move_count >= LMR_R2) {
          next_reduction = 2;
        } else {
          next_reduction = 1;
        }
      }
#if PARALLEL
      cilk_spawn
          subtree_scout(mv_index, move_list, ply, node_count_serial,
                        node_count, p, depth, beta, &aborted, &local_mutex,
                        &best_score, &best_move_index, pv, quiescence, np,
                        ext, mv, next_reduction, killer, best_move_history);

      if (is_aborted(&aborted)) {
        break;
      } else {
        continue;
      }
#else
      score = -scout_search(&np, -(beta - 1), ext + depth - 1, ply + 1, next_reduction,
                            subpv, node_count_serial, node_count, 
                            killer, best_move_history,
                            parent_abort);

#if TIMED_ABORTS
      if (abortf) {
        return 0;
      }
#endif

#endif
    }

    scored:
#if PARALLEL
    pthread_mutex_lock(&local_mutex);
#endif
    if (score > best_score) {
      best_score = score;
      best_move_index = mv_index;
      pv[0] = mv;
      // write best move into right position in PV buffer.
      memcpy(pv + 1, subpv, sizeof(move_t) * (MAX_PLY_IN_SEARCH - 1));
      pv[MAX_PLY_IN_SEARCH - 1] = 0;

      if (score >= beta) {
        if (mv != killer[KMT(ply,0)] && ENABLE_TABLES) {
          killer[KMT(ply,1)] = killer[KMT(ply,0)];
          killer[KMT(ply,0)] = mv;
        }
#if PARALLEL
        do_abort(&aborted);
        pthread_mutex_unlock(&local_mutex);
#endif
        break;
      }
    }
#if PARALLEL
    pthread_mutex_unlock(&local_mutex);
#endif
  }

#if PARALLEL
  cilk_sync;
#endif

  if (quiescence == false) {
    if (mv_index < num_of_moves) {
      mv_index++;   // moves tried
    }
    if (ENABLE_TABLES) update_best_move_history(p, best_move_index, move_list, mv_index, best_move_history);
  }
  tbassert(abs(best_score) != -INF, "best_score = %d\n", best_score);

  if (!TEST) {
    if (best_score < beta) {
      tt_hashtable_put(p->key, depth,
          tt_adjust_score_for_hashtable(best_score, ply), UPPER, 0);
    } else {
    tt_hashtable_put(p->key, depth,
        tt_adjust_score_for_hashtable(best_score, ply), LOWER, pv[0]);
    }
  }

  return best_score;
}

void subtree_scout( int mv_index, sortable_move_t *move_list, int ply,
                    uint64_t * node_count_serial, Speculative_add *node_count, position_t *p, int depth,
                    score_t beta, Abort *abort, pthread_mutex_t *local_mutex,
                    score_t *best_score, int *best_move_index, move_t *pv, bool quiescence,
                    position_t np, int ext, move_t mv, int next_reduction,
                    move_t * killer, int * best_move_history) {
    score_t score = 0;
    move_t subpv[MAX_PLY_IN_SEARCH];
    subpv[0] = 0;

    score = -scout_search(  &np, -(beta - 1), ext + depth - 1, ply + 1, next_reduction,
                            subpv, node_count_serial, node_count, 
                            killer, best_move_history,
                            abort);

    pthread_mutex_lock(local_mutex);
    // compare score to best score
    if (score > *best_score) {
      *best_score = score;
      *best_move_index = mv_index;
      pv[0] = mv;
      // write best move into right position in PV buffer.
      memcpy(pv+1, subpv, sizeof(move_t) * (MAX_PLY_IN_SEARCH - 1));
      pv[MAX_PLY_IN_SEARCH - 1] = 0;

      if (score >= beta) {
        if (mv != killer[KMT(ply,0)] && ENABLE_TABLES) {
          killer[KMT(ply,1)] = killer[KMT(ply,0)];
          killer[KMT(ply,0)] = mv;
        }
        do_abort(abort);
      }
    }
    pthread_mutex_unlock(local_mutex);

  return;
}


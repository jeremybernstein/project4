
// Copyright (c) 2013 MIT License, Tim Kaler
// Fa2013 - moved to C by Chris Fletcher

#include "speculative_add.h"
#include "stdlib.h"

// -----------------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------------

void spec_add(Speculative_reducer * sr, int a) {
  sr->real_total += a;
  if (sr->abort_flag) return;
  sr->value += a;
}

void reducer_abort(Speculative_reducer * sr) {
  sr->abort_flag = sr->deterministic;
  sr->last_value = sr->value;
}

void reducer_reset_abort(Speculative_reducer * sr) {
  sr->abort_flag = 0;
  return;
}

uint64_t reducer_get_value(Speculative_reducer * sr) {
  return sr->value;
}

// -----------------------------------------------------------------------------
// Reducer interface
// -----------------------------------------------------------------------------

void speculative_add_identity(void* key, void* value) {
  Speculative_reducer * rnew = (Speculative_reducer *) value;
  rnew->value = 0;
  rnew->last_value = 0; 
  rnew->abort_flag = 0; 
  rnew->reset_flag = 0; 
  rnew->deterministic = 0; 
  rnew->real_total = 0;
}

void speculative_add_reduce(void* key, void* left_v, void* right_v) {
  Speculative_reducer * left = (Speculative_reducer *) left_v;
  Speculative_reducer * right = (Speculative_reducer *) right_v;

  left->real_total += right->real_total;
//  if (!abort_flag) {
//    value += right->value;
//  }
//  if (right->abort_flag) {
//    abort_flag = true;
//  }

  if (!right->abort_flag) {
    // Neither reset nor abort, just add.
    // Left: X, Right: X
    if (!right->reset_flag && !left->abort_flag) {
      left->value += right->value;
      return;
    }

  // We've aborted, and there was no reset, don't add.
  // Left: A, Right: X
  if (!right->reset_flag && left->abort_flag) {
    return;
  }

  // The right has reset we've not aborted.
  // Left: X, Right: R
  if (right->reset_flag && !left->abort_flag) {
    reducer_reset_abort(left);
    left->value = right->value;
    return;
  }

  // The right has reset, and we've aborted.
  // Left: A, Right: R
  if (right->reset_flag && left->abort_flag) {
    reducer_reset_abort(left);
    left->value += right->value;
    return;
  }
  } else {
    // right has aborted.

    // Neither reset nor abort, just add.
    // Left: X, Right: A
    if (!right->reset_flag && !left->abort_flag) {
      left->value += right->value;
      reducer_abort(left);
      return;
    }

    // We've aborted, and there was no reset, don't add.
    // Left: A, Right: A
    if (!right->reset_flag && left->abort_flag) {
      return;
    }

    // The right has reset we've not aborted.
    // Left: X, Right: R A
    if (right->reset_flag && !left->abort_flag) {
      reducer_reset_abort(left);
      left->value += right->value;
      reducer_abort(left);
      return;
    }

    // The right has reset, and we've aborted.
    // Left: A, Right: R A
    if (right->reset_flag && left->abort_flag) {
      reducer_reset_abort(left);
      left->value += right->value;
      reducer_abort(left);
      return;
    }
  }
}

void speculative_add_destroy(void* key, void* value) {
  
}


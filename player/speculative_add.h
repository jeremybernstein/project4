// Copyright (c) 2013 MIT License, Tim Kaler
// Fa2013 - moved to C by Chris Fletcher

#ifndef SPECULATIVE_ADD_H
#define SPECULATIVE_ADD_H

#include <stdlib.h>
#include <cilk/cilk.h>
#include <cilk/reducer.h>

struct Speculative_reducer {
  uint64_t value;
  int abort_flag;
  int reset_flag;
  uint64_t last_value;
  uint64_t real_total;
  int deterministic;
};
typedef struct Speculative_reducer Speculative_reducer;

void spec_add(Speculative_reducer * sr, int a);
uint64_t reducer_get_value(Speculative_reducer * sr);

void speculative_add_reduce(void* key, void* left, void* right);
void speculative_add_identity(void* key, void* value);
void speculative_add_destroy(void* key, void* value);

typedef CILK_C_DECLARE_REDUCER(Speculative_reducer) Speculative_add;

#endif

#include "set.h"

int test_next_state(int state, int add) {
  if (add == 1) {
    state = state + 1;
  } else {
    if (state > 0) {
      state = state - 1;
    }
  }
  
  return state;
}

int test_response(int state, int add) {
  return 123;
}

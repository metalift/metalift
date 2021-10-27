#include "set.h"

set* test_next_state(set* state, int add, int value) {
  if (add == 1) {
    state = set_add(state, value);
  } else {
    state = set_remove(state, value);
  }
  
  return state;
}

int test_response(set* state, int add, int value) {
  return 123;
}

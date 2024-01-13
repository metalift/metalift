#include "set.h"

set* test(set* s, int add, int value) {
  if (add == 1) {
    s = set_add(s, value);
  } else {
    s = set_remove(s, value);
  }

  return s;
}

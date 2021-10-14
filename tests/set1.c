#include "set.h"

bool test(int i) {
  set* s = set_create();
  s = set_add(s, 1);
  s = set_add(s, 2);
  s = set_add(s, 3);
  return set_contains(s, i);
}

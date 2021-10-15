#include "set.h"

set* test(int a) {
  set* s = set_create();
  s = set_add(s, 1);
  s = set_add(s, 2);
  s = set_add(s, 3);
  if (a == 1 || a == 2 || a == 3) {
    s = set_add(s, a);
  }
  return s;
}

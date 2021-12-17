// tuple test
#include  "tuples.h"
int test(int x, int y) {
  Tuple<int,int> u = mktuple(x,x);
  Tuple<int,int> v = mktuple(y,y);
  int z = tupleGet(u,0) + tupleGet(u,1) + tupleGet(v,0) + tupleGet(v,1);
  return z;
} 
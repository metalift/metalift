// tuple test
#include  "tuples.h"
int test(int x, int y) {
  Tuple<int,int> u = MakeTuple(x,x);
  Tuple<int,int> v = MakeTuple(y,y);
  int z = tupleGet(u,0) + tupleGet(u,1) + tupleGet(v,0) + tupleGet(v,1);
  return z;
}

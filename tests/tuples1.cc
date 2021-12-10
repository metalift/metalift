// tuple test
#include  "tuples.h"
int test(int x, int y) {
  	Tuple<int,int> v = mktuple(x,x);
	Tuple<int,int> w = mktuple(y,y);
	int a = tupleGet(v,0) + tupleGet(w,1);
  return a;
}
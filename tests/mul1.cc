#include "list.h"
//#include <iostream>
//#include <vector>
//#include <string>

// Assume length must be equal
// This will be enforced for synthesis & verification by ignoring in the grammar
extern "C" List<int> test(List<int> left, List<int> right)
{
  int length = listLength(left);
  List<int> prod = newList<int>();
  for (int i = 0; i < length; i++) {
    prod = listAppend(prod, listGet(left, i) * listGet(right, i));
  }

  return prod;
}

//int main(int argc, char** argv) {
//	List<int> l = newList<int>();
//	l = listAppend(l, 1);
//	l = listAppend(l, 2);
//	List<int> r = newList<int>();
//	r = listAppend(r, 3);
//	r = listAppend(r, 4);
//	List<int> o = test(l, r);
//
//	for (std::vector<int>::const_iterator i = o->contents.begin(); i != o->contents.end(); ++i)
//		std::cout << *i << std::endl;
//
//	return 0;
//
//}

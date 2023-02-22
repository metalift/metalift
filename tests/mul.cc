#include "list.h"
//#include <iostream>
//#include <vector>
//#include <string>

extern "C" List<int> test(List<int> left, List<int> right)
{
  int leftLength = listLength(left);
  int rightLength = listLength(right);
  // Ignore elements beyond last element of smaller list
  //int minlen = leftLength < rightLength ? leftLength : rightLength;
  //int minlen = leftLength;
  //if (rightLength < leftLength)
  //  minlen = rightLength;
  //int minlen = 3;
  List<int> prod = newList<int>();
  // We can assume the lengths are well-behaved
  for (int i = 0; i < leftLength; ++i)
	prod = listAppend(prod, listGet(left, i) * listGet(right, i));

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

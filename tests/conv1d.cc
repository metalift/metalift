#include "list.h"
//#include <iostream>
//#include <vector>
//#include <string>

// Assume length must be equal
// This will be enforced for synthesis & verification by ignoring in the grammar
extern "C" List<int> test(List<int> vec, List<int> kernel)
{
  int slides = listLength(vec) - listLength(kernel) + 1;
  int kernelLength = listLength(kernel);
  List<int> convolved = newList<int>();
  for (int i = 0; i < slides; i++) {
    int dot_product = 0;
    for (int j = 0; j < kernelLength; j++) {
      dot_product += listGet(vec, i + j) * listGet(kernel, j);
    }
    convolved = listAppend(convolved, dot_product);
  }

  return convolved;
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

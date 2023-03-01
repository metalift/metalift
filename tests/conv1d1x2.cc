#include <iostream>
#include <vector>
#include <string>
#include "list.h"

// Assume kernel has length 2
extern "C" List<int> test(List<int> vec, List<int> kernel)
{
  int slides = listLength(vec) - 1;
  int kernelLength = 2;
  List<int> convolved = newList<int>();
  for (int i = 0; i < slides; i++) {
    int element1 = listGet(vec, i) * listGet(kernel, 0);
    int element2 = listGet(vec, i + 1) * listGet(kernel, 1);
    int dot_product = element1 + element2;
    convolved = listAppend(convolved, dot_product);
  }

  return convolved;
}

//int main(int argc, char** argv) {
//	List<int> l = newList<int>();
//	l = listAppend(l, 1);
//	l = listAppend(l, 2);
//	l = listAppend(l, 1);
//	l = listAppend(l, 2);
//	List<int> r = newList<int>();
//	r = listAppend(r, 3);
//	r = listAppend(r, 4);
//	List<int> o = test(l, r);
//
//	std::cout << o->contents[0] << std::endl;
//
//	return 0;
//
//}

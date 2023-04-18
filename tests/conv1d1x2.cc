#include <iostream>
#include <vector>
#include <string>
#include "list.h"

// Assume kernel has length 2
//extern "C" List<int> test(List<int> vec, List<int> kernel)
//{
//  int slides = listLength(vec) - 1;
//  List<int> convolved = newList<int>();
//  for (int i = 0; i < slides; i++) {
//    //int element1 = listGet(vec, i) * listGet(kernel, 0);
//    //int element2 = listGet(vec, i + 1) * listGet(kernel, 1);
//    //int dot_product = element1 + element2;
//    //convolved = listAppend(convolved, dot_product);
//    convolved = listAppend(convolved, listGet(vec, i) * listGet(kernel, 0) + listGet(vec, i+1) * listGet(kernel, 1));
//  }
//
//  return convolved;
//}
extern "C" List<int> test(List<int> vec)
{
  int slides = listLength(vec) - 1;
  List<int> convolved = newList<int>();
  for (int i = 0; i < slides; i++) {
    //int element1 = listGet(vec, i) * listGet(kernel, 0);
    //int element2 = listGet(vec, i + 1) * listGet(kernel, 1);
    //int dot_product = element1 + element2;
    //convolved = listAppend(convolved, dot_product);
    convolved = listAppend(convolved, listGet(vec, i) + listGet(vec, i+1));
  }

  return convolved;
}

int main(int argc, char** argv) {
	List<int> l = newList<int>();
  for (int i = 0; i < 10000; i++) {
  	l = listAppend(l, i);
  }
	List<int> o = test(l);

  std::cout << "[";
  for (int i = 0; i < 9; i++) {
	  std::cout << o->contents[i] << ", ";
  }
  std::cout << "]" << std::endl;
	return 0;

}

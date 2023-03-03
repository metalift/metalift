#include "list.h"
//#include <iostream>
//#include <vector>
//#include <string>

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

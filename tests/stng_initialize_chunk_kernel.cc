#include <iostream>
#include <vector>
#include <string>
#include "list.h"

// Assume kernel has length 2
extern "C" List<int> test(List<int> vertexx)
{
  int x_max = listLength(vec) - 1;
  List<int> cellx = newList<int>();
  for (int j = 0; j < x_max; j++) {
    cellx = listAppend(cellx, listGet(vertexx, j) + listGet(vertexx, j + 1));
  }

  return cellx;
}

#include <iostream>
#include <vector>
#include <string>
#include "list.h"

extern "C" List<int> test(List<int> vec)
{
  int slides = listLength(vec) - 1;
  List<int> convolved = newList<int>();
  for (int i = 0; i < slides; i++) {
    convolved = listAppend(convolved, 2 * listGet(vec, i) - listGet(vec, i+1));
  }

  return convolved;
}

int main(int argc, char** argv) {
	List<int> l = newList<int>();
  for (int i = 0; i < 100000; i++) {
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

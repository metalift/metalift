#include <iostream>
#include <vector>
#include <string>
#include "list.h"

extern "C" List<int> test(List<int> vec)
{
  int slides = listLength(vec) - 1;
  List<int> convolved = newList<int>();
  for (int i = 0; i < slides; i++) {
    convolved = listAppend(convolved, listGet(vec, i) + listGet(vec, i+1));
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

int main_n(int argc, char** argv) {
  std::vector<int> vec(10000000, 0);
  for (int i = 0; i < 10000000; i++) {
    vec[i] = i;
  }

  // test() in pure c++
  int slides = int(vec.size()) - 1;
  std::vector<int> convolved;
  for (int i = 0; i < slides; i++) {
    convolved.push_back(vec[i] + vec[i+1]);
  }

  std::cout << "[";
  for (int i = 0; i < convolved.size(); i++) {
    std::cout << convolved[i] << ", ";
  }
  std::cout << "]" << std::endl;
  return 0;
}

#define LEN 10
#define SLIDES (LEN - 1)

int main_c(int argc, char** argv) {
  int vec[LEN];
  for (int i = 0; i < LEN; i++) {
    vec[i] = i;
  }

  int convolved[SLIDES];
  for (int i = 0; i < SLIDES; i++) {
    convolved[i] = vec[i] + vec[i+1];
  }
}

#include "list.h"
#include <iostream>

List test(List in)
{
  List out = newList();
  for (int i = 0; i < listLength(in); ++i) {
    if (listGet(in, i) > 2)
      out = listAppend(out, listGet(in, i));
  }

  return out;
}

// test code
int main (int argc, char ** argv)
{
  List l = newList();
  l = listAppend(l, 1);
  l = listAppend(l, 20);
  List r = test(l);

  for (std::vector<int>::const_iterator i = r->contents.begin(); i != r->contents.end(); ++i)
    std::cout << *i << std::endl;

  return 0;
}

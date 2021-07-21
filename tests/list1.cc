#include "list.h"
#include <iostream>

List test(List in)
{
  List out = newList();
  for (int i = 0; i < listLength(in); ++i)
    out = listAppend(out, listGet(in, i));

  return out;
}

// test code
int main (int argc, char ** argv)
{
  List l = newList();
  l = listAppend(l, 1);
  l = listAppend(l, 2);
  List r = test(l);

  for (std::vector<int>::const_iterator i = l->contents.begin(); i != l->contents.end(); ++i)
    std::cout << *i << std::endl;

  return 0;
}

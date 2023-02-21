#include "list.h"

extern "C" List<int> test(List<int> in)
{
  List<int> out = newList<int>();
  for (int i = 1; i < listLength(in); ++i)
	out = listAppend(out, listGet(in, i));

  return out;
}


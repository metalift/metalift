#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "list.h"

List test (List in) 
{
  List out = newList();
  for (int i = 0; i < listLength(in); ++i) 
    out = listAppend(out, listGet(in, i));

  return out;
}

int main (int argc, char ** argv) 
{
  List l = newList();
  l = listAppend(l, 10);
  l = listAppend(l, 20);
  
  List r = test(l);

  for (int i = 0; i < listLength(r); ++i)
    printf("%d: %d\n", i, listGet(r, i));

  return 0;
}


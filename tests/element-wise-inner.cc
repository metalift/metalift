//element-wise multiplication 

#include "list.h"

extern "C" List<int> test(List<int> a, List<int> b)
{
        List<int> c = newList<int>();
    
        for (int j = 0; j < listLength(a); j++)
        {
            c = listAppend(c,listGet(a,j)*listGet(b,j));
        }
        return c;
  
}

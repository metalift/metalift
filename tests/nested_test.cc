#include "list.h"
#include "matrix.h"


extern "C" List<int> test(nestedList<int> data)
{
		List<int> fit = newList<int>();
        //creating new nested list
        //nestedList<int> data2 = nestednewList<int>();
        for(int i=0; i<nestedLength(data); i++)
            fit = listAppend(fit,2*listGet(nestedGet(data,i),0));
            // appending to nested list
            // data2 = nestedAppend(data2,fit);   
        return fit;

}
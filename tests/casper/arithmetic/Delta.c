#include "list.h"
#include <iostream>


int test(List<int> data) {
	int min = __INT_MAX__;
	int max = __INT_MIN__;
	for(int i=0; i<listLength(data); i++) {
		int val = listGet(data,i);
		if(max < val)
			max = val;
		if(min > val)
			min = val;
	}
	return max-min;
}

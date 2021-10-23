#include "list.h"
#include <iostream>


int test(List<int> data) {
	int min = __INT_MAX__;
	for(int i=0; i<listLength(data); i++) {
		int val = listGet(data, i);
		if(min > val)
			min = val;
	}
	return min;
}

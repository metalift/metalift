#include "list.h"
#include <iostream>


int test(List<int> data) {
	int max = __INT_MIN__;
	for(int i=0; i<listLength(data); i++) {
		int val = abs(listGet(data,i));
		if(max < val)
			max = val;
	}
	return max;
}

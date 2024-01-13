#include "list.h"
#include <iostream>


int test(List<int> data) {
	int sum = 0;
	for(int i=0; i<listLength(data); i++) {
		sum += listGet(data,i);
	}
	return sum;
}

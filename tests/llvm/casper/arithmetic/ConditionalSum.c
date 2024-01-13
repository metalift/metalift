#include "list.h"
#include <iostream>


int test(List<int> data) {
	int sum = 0;
	for(int i=0; i<listLength(data); i++) {
		int var = listGet(data,i);
		if(var < 100){
			sum += var;
		}
	}
	return sum;
}

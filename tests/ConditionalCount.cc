#include "list.h"
#include <iostream>


int test(List<int> data) {
	int count = 0;
	for(int i=0; i<listLength(data); i++) {
		int var = listGet(data,i);
		if(var < 100){
			count++;
		}
	}
	return count;
}


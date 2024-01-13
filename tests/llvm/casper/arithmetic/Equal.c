#include "list.h"
#include <iostream>


bool test(List<int> data, int val) {
	bool equal = true;
	for(int i=0; i<listLength(data); i++) {
		if(val != listGet(data,i)){
			equal = false;
		}
	}
	return equal;
}

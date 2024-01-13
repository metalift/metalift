#include "list.h"
#include <iostream>


bool equalFrequency(List<int> data) {
	int first = 0;
	int second = 0;
	for(int i=0; i<listLength(data); i++) {
		int var = listLength(data,i);
		if(var == 100){
			first++;
		}
		if(var == 110){
			second++;
		}
	}
	return first == second;
}

#include "list.h"
#include <iostream>

int test(List<int> data) {
		int sum = 0;
		int count = 0;
		for(int i=0; i<listLength(data); i++) {
			sum += listGet(data, i);
			count++;
		}
		return sum / count;
}

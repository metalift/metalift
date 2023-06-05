#include "list.h"
#include <iostream>



List<List<int>> main(List<List<int>> image, List<int> hR, List<int> hG, List<int> hB) {
	for (int i = 0; i < listLength(image); i += 1) {
		int r = listGet(listGet(image,i),0);
		int g = listGet(listGet(image,i),1);
		int b = listGet(listGet(image,i),2);
		listGet(hR,r)= listGet(hR,r)+1;
		listGet(hG,g)= listGet(hG,g)+1;
		listGet(hB,b)= listGet(hB,b)+1;
	}

	List<List<int>> result = newList<List<int>>()
	listAppend(result,hR);
	listAppend(result,hG);
	listAppend(result,hB);

	return result;
}


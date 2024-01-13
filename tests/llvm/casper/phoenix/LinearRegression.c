#include "list.h"
#include <iostream>

List<int> main (List<List<int>> points) {
	int SX_ll = 0, SY_ll = 0, SXX_ll = 0, SYY_ll = 0, SXY_ll = 0;

	// ADD UP RESULTS
	for (int i = 0; i < listLength(data); i++) {
		// Compute SX, SY, SYY, SXX, SXY
		SX_ll += listGet(listGet(points, i), 0);
		SXX_ll += listGet(listGet(points, i), 0) * listGet(listGet(points, i), 0);
		SY_ll += listGet(listGet(points, i), 1);
		SYY_ll += listGet(listGet(points, i), 1) * listGet(listGet(points, i), 1);
		SXY_ll += listGet(listGet(points, i), 0) * listGet(listGet(points, i), 1);
	}
	List<int> result = newList<int>()
	listAppend(result, SX_ll);
	listAppend(result, SXX_ll);
	listAppend(result, SY_ll);
	listAppend(result, SYY_ll);
	listAppend(result, SXY_ll);
	return result;
}

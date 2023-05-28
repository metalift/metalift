#include "list.h"

extern "C" int test(List<int> lst) {
    int sum = 0;
    for (int i = 0; i < listLength(lst); ++i) {
        int curr_el = listGet(lst, i);
        if (curr_el < 0) {
            sum += -curr_el;
        } else {
            sum += curr_el;
        }
    }
    return sum;
}

#include "list.h"

extern "C" int forward_sum(List<int> lst) {
    int lst_abs_sum_forward = 0;
    for (int i = 0; i < listLength(lst); ++i) {
        int curr_el = listGet(lst, i);
        if (curr_el < 0) {
            lst_abs_sum_forward += -curr_el;
        } else {
            lst_abs_sum_forward += curr_el;
        }
    }
    return lst_abs_sum_forward;
}

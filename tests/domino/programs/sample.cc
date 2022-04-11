// Sample every 30th packet in a flow
#define N 30
#include "list.h"

extern "C" List<int> test(int count, int sample) {
    if (count == N - 1) {
        sample = 1;
        count = 0;
    } else {
        sample = 0;
        count = count + 1;
    }

    List<int> out = newList<int>();
    out = listAppend(out, sample);
    out = listAppend(out, count);
    return out;
}

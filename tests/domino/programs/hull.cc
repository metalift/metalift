#include "list.h"
#define DRAIN_RATE 10
#define ECN_THRESH 20

/* int counter = ECN_THRESH;
int last_time = 0; */

/* struct Packet
{
    int bytes;
    int time;
    int mark;
}; */

extern "C" List<int> test(int counter, int last_time, int mark, int bytes, int time)
{
    // Decrement counter according to drain rate
    // counter = counter - (time - last_time) * DRAIN_RATE;

    if (counter < 0)
        counter = 0;
    else
        counter = counter;

    // Increment counter
    counter += bytes;

    // If we are above the ECN_THRESH, mark
    // if (counter > ECN_THRESH)
    if (mark > ECN_THRESH)
        mark = 1;
    else
        mark = mark;

    // Store last time
    last_time = time;

    List<int> out = newList<int>();
    out = listAppend(out, counter);
    out = listAppend(out, last_time);
    out = listAppend(out, mark);
    return out;
}

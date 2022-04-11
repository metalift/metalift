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

extern "C" List<int> stage0(int time, int last_time) {
    List<int> out = newList<int>();
    out = listAppend(out, (time - last_time) * DRAIN_RATE);
    return out;
}

extern "C" List<int> stage1(int counter, int stage_1_output) {
    List<int> out = newList<int>();
    out = listAppend(out, counter - stage_1_output);
    return out;
}

extern "C" List<int> stage2(int counter_after_stage_1, int bytes) {
    if (counter_after_stage_1 < 0)
        counter_after_stage_1 = 0;
    else
        counter_after_stage_1 = counter_after_stage_1;

    // Increment counter_after_stage_1
    counter_after_stage_1 += bytes;

    List<int> out = newList<int>();
    out = listAppend(out, counter_after_stage_1);
    return out;
}

extern "C" List<int> stage3(int mark, int counter_after_stage_2) {
    // If we are above the ECN_THRESH, mark
    if (counter_after_stage_2 > ECN_THRESH)
        mark = 1;
    else
        mark = mark;

    List<int> out = newList<int>();
    out = listAppend(out, mark);
    return out;
}

extern "C" List<int> stage4(int counter_after_stage_2, int mark_after_stage_3,
                            int last_time, int time) {
    // Store last time
    last_time = time;

    List<int> out = newList<int>();
    out = listAppend(out, counter_after_stage_2);
    out = listAppend(out, last_time);
    out = listAppend(out, mark_after_stage_3);
    return out;
}

/*
extern "C" List<int> test(int counter, int last_time, int mark, int bytes,
                          int time) {
    // Decrement counter according to drain rate
    counter = counter - (time - last_time) * DRAIN_RATE;

    if (counter < 0)
        counter = 0;
    else
        counter = counter;

    // Increment counter
    counter += bytes;

    // If we are above the ECN_THRESH, mark
    if (counter > ECN_THRESH)
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
*/

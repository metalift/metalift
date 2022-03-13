#include "list.h"
#define ALPHA 5
#define GAMMA 2
#define CAPACITY 10
#define BUFFER 3

extern "C" List<int> stage0p1(int vq, int capacity, int time, int last_time) {
    List<int> out = newList<int>();
    out = listAppend(out, vq - capacity * (time - last_time));
    return out;
}

extern "C" List<int> stage0(int cond_stage_0p1) {
    int vq;
    if (cond_stage_0p1 < 0) {
        vq = 0;
    } else {
        vq = cond_stage_0p1;
    }

    List<int> out = newList<int>();
    out = listAppend(out, vq);
    return out;
}

/*
extern "C" List<int> test(int vq, int capacity, int last_time, int bytes,
                          int time, int mark, int min, int max, int max_vq) {
    // Update virtual queue size
    vq = ((vq - capacity * (time - last_time)) < 0)
             ? 0
             : (vq - capacity * (time - last_time));

    // Mark or drop packet in real queue
    if (vq + bytes > BUFFER) {
        mark = 1;
    } else {
        vq = vq + bytes;
    }

    // Update virtual capacity
    min =
        ((capacity + ALPHA * GAMMA * CAPACITY * (time - last_time)) < CAPACITY)
            ? (capacity + ALPHA * GAMMA * CAPACITY * (time - last_time))
            : CAPACITY;
    max = (min - ALPHA * bytes < 0) ? 0 : min - ALPHA * bytes;
    capacity = max;

    last_time = time;

    List<int> out = newList<int>();
    out = listAppend(out, min);
    out = listAppend(out, max);
    out = listAppend(out, capacity);
    out = listAppend(out, last_time);
    return out;
}
*/

#include "list.h"
#define ALPHA 10
#define GAMMA 10
#define CAPACITY 20
#define BUFFER 20

extern "C" List<int> stage0p1(int vq, int capacity, int time, int last_time) {
    /*
    vq = ((vq - capacity * (p.time - last_time)) < 0) ? 0 : (vq - capacity
     * (p.time - last_time));
    */
    List<int> out = newList<int>();
    out = listAppend(out, capacity * (time - last_time));
    return out;
}

extern "C" List<int> stage0p2(int vq, int p1_output) {
    /*
    vq = ((vq - capacity * (p.time - last_time)) < 0) ? 0 : (vq - capacity
     * (p.time - last_time));
    */
    List<int> out = newList<int>();
    out = listAppend(out, vq - p1_output);
    return out;
}

extern "C" List<int> stage0p3(int p2_output) {
    /*
    vq = ((vq - capacity * (p.time - last_time)) < 0) ? 0 : (vq - capacity
     * (p.time - last_time));
    */

    int vq;
    if (p2_output < 0) {
        vq = 0;
    } else {
        vq = p2_output;
    }

    List<int> out = newList<int>();
    out = listAppend(out, vq);
    return out;
}

extern "C" List<int> stage1p1(int vq_stage_0, int bytes) {
    /*
    if (vq + p.bytes > BUFFER) {
    */
    List<int> out = newList<int>();
    out = listAppend(out, vq_stage_0 + bytes);
    return out;
}

extern "C" List<int> stage1p2(int vq_stage_0, int p1_output, int mark) {
    /*
    // Mark or drop packet in real queue
    if (vq + p.bytes > BUFFER) {
        p.mark = 1;
    } else {
        vq = vq + p.bytes;
    }
    */
    if (p1_output > BUFFER) {
        mark = 1;
    } else {
        vq_stage_0 = p1_output;
    }

    List<int> out = newList<int>();
    out = listAppend(out, vq_stage_0);
    out = listAppend(out, mark);
    return out;
}

extern "C" List<int> stage2p1(int time, int last_time) {
    /*
    // Update virtual capacity
  p.min = ((capacity + ALPHA * GAMMA * CAPACITY * (p.time - last_time)) <
CAPACITY) ? (capacity + ALPHA * GAMMA * CAPACITY * (p.time - last_time)) :
CAPACITY;
    */
    List<int> out = newList<int>();
    out = listAppend(out, ALPHA * GAMMA * CAPACITY * (time - last_time));
    return out;
}

extern "C" List<int> stage2p2(int capacity, int p1_output) {
    /*
    // Update virtual capacity
  p.min = ((capacity + ALPHA * GAMMA * CAPACITY * (p.time - last_time)) <
CAPACITY) ? (capacity + ALPHA * GAMMA * CAPACITY * (p.time - last_time)) :
CAPACITY;
    */
    List<int> out = newList<int>();
    out = listAppend(out, capacity + p1_output);
    return out;
}

extern "C" List<int> stage2p3(int p2_output) {
    /*
    // Update virtual capacity
    p.min = ((capacity + ALPHA * GAMMA * CAPACITY * (p.time - last_time)) <
    CAPACITY) ? (capacity + ALPHA * GAMMA * CAPACITY * (p.time - last_time)) :
    CAPACITY;
    */
    int min;
    if (p2_output < CAPACITY) {
        min = p2_output;
    } else {
        min = p2_output;
    }

    List<int> out = newList<int>();
    out = listAppend(out, min);
    return out;
}

extern "C" List<int> stage3p1(int min, int bytes) {
    /*
    p.max = (p.min - ALPHA * p.bytes < 0) ? 0 : p.min - ALPHA * p.bytes;
    */
    List<int> out = newList<int>();
    out = listAppend(out, min - ALPHA * bytes);
    return out;
}

extern "C" List<int> stage3p2(int p1_output) {
    /*
    p.max = (p.min - ALPHA * p.bytes < 0) ? 0 : p.min - ALPHA * p.bytes;
    */
    int max;
    if (p1_output < 0) {
        max = 0;
    } else {
        max = p1_output;
    }

    List<int> out = newList<int>();
    out = listAppend(out, max);
    return out;
}

extern "C" List<int> stage4(int max, int time) {
    /*
    capacity = p.max;
    last_time = p.time;
    */
    int capacity = max;
    int last_time = time;

    List<int> out = newList<int>();
    out = listAppend(out, capacity);
    out = listAppend(out, last_time);
    return out;
}

/*
struct Packet {
  int bytes;
  int time;
  int mark;
  int min;
  int max;
  int max_vq;
};

int vq = 0;
int capacity = 0;
int last_time = 0;

void func(struct Packet p) {
  // Update virtual queue size
  vq = ((vq - capacity * (p.time - last_time)) < 0) ? 0 : (vq - capacity *
(p.time - last_time));

  // Mark or drop packet in real queue
  if (vq + p.bytes > BUFFER) {
    p.mark = 1;
  } else {
    vq = vq + p.bytes;
  }

  // Update virtual capacity
  p.min = ((capacity + ALPHA * GAMMA * CAPACITY * (p.time -last_time)) <
CAPACITY) ? (capacity + ALPHA * GAMMA * CAPACITY * (p.time -last_time)) :
CAPACITY;
  p.max = (p.min - ALPHA * p.bytes < 0) ? 0 : p.min - ALPHA * p.bytes;
  capacity = p.max;

  last_time = p.time;
}
*/

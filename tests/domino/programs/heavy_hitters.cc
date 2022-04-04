#include "list.h"
#define low_th 10
#define hi_th 20

/* These functions are uninterpreted, hence the no-op implementations */
extern "C" int uninterpHash2a(int sport, int dport) { return -1000000; }
extern "C" int uninterpHash2b(int sport, int dport) { return -2000000; }
extern "C" int uninterpHash2c(int sport, int dport) { return -3000000; }
extern "C" int uninterpReadSketch1At(int idx) { return -10000001; }
extern "C" int uninterpReadSketch2At(int idx) { return -20000002; }
extern "C" int uninterpReadSketch3At(int idx) { return -30000003; }

/**
 * The actual benchmark functions.
 * Note: We assume that the returned sketch{1,2,3}_idx values
 * will be set to 1 in the outside function (to work around
 * need for random-access to arrays). We further elide the modulo
 * operation away since none of the Domino atoms have modulo
 * as a valid operation.
 */
extern "C" List<int> stage0(int sport, int dport) {
    int sketch1_idx = uninterpHash2a(sport, dport);
    int sketch2_idx = uninterpHash2b(sport, dport);
    int sketch3_idx = uninterpHash2c(sport, dport);

    List<int> out = newList<int>();
    out = listAppend(out, sketch1_idx);
    out = listAppend(out, sketch2_idx);
    out = listAppend(out, sketch3_idx);
    return out;
}

extern "C" List<int> stage1(int sketch1_idx, int sketch2_idx, int sketch3_idx) {
    List<int> out = newList<int>();
    out = listAppend(out, uninterpReadSketch1At(sketch1_idx));
    out = listAppend(out, uninterpReadSketch2At(sketch2_idx));
    out = listAppend(out, uninterpReadSketch3At(sketch3_idx));
    return out;
}

extern "C" List<int> stage2p1p1(int val_at_sketch2, int val_at_sketch3) {
    int member;
    if (val_at_sketch2 > low_th) {
        if (val_at_sketch3 > low_th) {
            member = 1;
        } else {
            member = 0;
        }
    } else {
        member = 0;
    }

    List<int> out = newList<int>();
    out = listAppend(out, member);
    return out;
}

extern "C" List<int> stage2p1p2(int val_at_sketch1, int p1_output) {
    int member;
    /*
    sketch_cnt_1[p.sketch1_idx] > low_th && sketch_cnt_1[p.sketch1_idx] <
hi_th && sketch_cnt_2[p.sketch2_idx] > low_th && sketch_cnt_2[p.sketch2_idx] <
hi_th && sketch_cnt_3[p.sketch3_idx] > low_th && sketch_cnt_3[p.sketch3_idx] <
hi_th
    */
    if (val_at_sketch1 > low_th) {
        if (p1_output > 0) {
            member = 1;
        } else {
            member = 0;
        }
    } else {
        member = 0;
    }

    List<int> out = newList<int>();
    out = listAppend(out, member);
    return out;
}

extern "C" List<int> stage2p2p1(int val_at_sketch2, int val_at_sketch3) {
    int member;
    /*
    sketch_cnt_1[p.sketch1_idx] > low_th && sketch_cnt_1[p.sketch1_idx] <
hi_th && sketch_cnt_2[p.sketch2_idx] > low_th && sketch_cnt_2[p.sketch2_idx] <
hi_th && sketch_cnt_3[p.sketch3_idx] > low_th && sketch_cnt_3[p.sketch3_idx] <
hi_th
    */
    if (val_at_sketch2 < hi_th) {
        if (val_at_sketch3 < hi_th) {
            member = 1;
        } else {
            member = 0;
        }
    } else {
        member = 0;
    }

    List<int> out = newList<int>();
    out = listAppend(out, member);
    return out;
}

extern "C" List<int> stage2p2p2(int val_at_sketch1, int p1_output) {
    int member;
    /*
    sketch_cnt_1[p.sketch1_idx] > low_th && sketch_cnt_1[p.sketch1_idx] <
hi_th && sketch_cnt_2[p.sketch2_idx] > low_th && sketch_cnt_2[p.sketch2_idx] <
hi_th && sketch_cnt_3[p.sketch3_idx] > low_th && sketch_cnt_3[p.sketch3_idx] <
hi_th
    */
    if (val_at_sketch1 < hi_th) {
        if (p1_output > 0) {
            member = 1;
        } else {
            member = 0;
        }
    } else {
        member = 0;
    }

    List<int> out = newList<int>();
    out = listAppend(out, member);
    return out;
}

extern "C" List<int> stage2p3(int output_of_stage2p1, int output_of_stage2p2) {
    int member;
    if (output_of_stage2p1 != 0) {
        if (output_of_stage2p2 != 0) {
            member = 1;
        } else {
            member = 0;
        }
    } else {
        member = 0;
    }

    List<int> out = newList<int>();
    out = listAppend(out, member);
    return out;
}

extern "C" List<int> stage3(int val_at_sketch1_idx, int val_at_sketch2_idx,
                            int val_at_sketch3_idx) {
    List<int> out = newList<int>();
    out = listAppend(out, val_at_sketch1_idx + 1);
    out = listAppend(out, val_at_sketch2_idx + 1);
    out = listAppend(out, val_at_sketch3_idx + 1);
    return out;
}

/*
struct Packet {
  int sport;
  int dport;
  int is_not_heavy_hitter;
  int sketch1_idx;
  int sketch2_idx;
  int sketch3_idx;
};

#define NUM_ENTRIES 4096

int sketch_cnt_1[NUM_ENTRIES] = {0};
int sketch_cnt_2[NUM_ENTRIES] = {0};
int sketch_cnt_3[NUM_ENTRIES] = {0};

void func(struct Packet p) {
  p.sketch1_idx = hash2a(p.sport, p.dport) % NUM_ENTRIES;
  p.sketch2_idx = hash2b(p.sport, p.dport) % NUM_ENTRIES;
  p.sketch3_idx = hash2c(p.sport, p.dport) % NUM_ENTRIES;
  if (sketch_cnt_1[p.sketch1_idx] > low_th && sketch_cnt_1[p.sketch1_idx] <
hi_th && sketch_cnt_2[p.sketch2_idx] > low_th && sketch_cnt_2[p.sketch2_idx] <
hi_th && sketch_cnt_3[p.sketch3_idx] > low_th && sketch_cnt_3[p.sketch3_idx] <
hi_th) { p.is_not_heavy_hitter = 0; }	else { p.is_not_heavy_hitter = 1;
  }
        sketch_cnt_1[p.sketch1_idx]+= 1;
        sketch_cnt_2[p.sketch2_idx]+= 1;
        sketch_cnt_3[p.sketch3_idx]+= 1;
}
*/

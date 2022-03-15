#include "list.h"

/* These functions are uninterpreted, hence the no-op implementations */
extern "C" int uninterpHash2a(int sport, int dport) { return -1000000; }
extern "C" int uninterpHash2b(int sport, int dport) { return -2000000; }
extern "C" int uninterpHash2c(int sport, int dport) { return -3000000; }
extern "C" int uninterpReadFilter1At(int idx) { return -10000001; }
extern "C" int uninterpReadFilter2At(int idx) { return -20000002; }
extern "C" int uninterpReadFilter3At(int idx) { return -30000003; }

/**
 * The actual benchmark functions.
 * Note: We assume that the returned filter{1,2,3}_idx values
 * will be set to 1 in the outside function (to work around
 * need for random-access to arrays). We further elide the modulo
 * operation away since none of the Domino atoms have modulo
 * as a valid operation.
 */
extern "C" List<int> stage0(int sport, int dport) {
    int filter1_idx = uninterpHash2a(sport, dport);
    // int filter2_idx = uninterpHash2b(sport, dport);
    // int filter3_idx = uninterpHash2c(sport, dport);

    List<int> out = newList<int>();
    out = listAppend(out, filter1_idx);
    // out = listAppend(out, filter2_idx);
    // out = listAppend(out, filter3_idx);
    return out;
}

extern "C" List<int> stage1(int filter1_idx, int filter2_idx, int filter3_idx) {
    List<int> out = newList<int>();
    out = listAppend(out, uninterpReadFilter1At(filter1_idx));
    out = listAppend(out, uninterpReadFilter2At(filter2_idx));
    out = listAppend(out, uninterpReadFilter3At(filter3_idx));
    return out;
}

extern "C" List<int> stage2(int val_at_filter1, int val_at_filter2,
                            int val_at_filter3) {
    int member =
        val_at_filter1 != 0 && val_at_filter2 != 0 && val_at_filter3 != 0;

    List<int> out = newList<int>();
    out = listAppend(out, member);
    return out;
}

/*
struct Packet {
    int sport;
    int dport;
    int member;
    int filter1_idx;
    int filter2_idx;
    int filter3_idx;
};

#define NUM_ENTRIES 256

int filter1[NUM_ENTRIES] = {0};
int filter2[NUM_ENTRIES] = {0};
int filter3[NUM_ENTRIES] = {0};

void func(struct Packet pkt) {
    pkt.filter1_idx = uninterpHash2a(pkt.sport, pkt.dport) % NUM_ENTRIES;
    pkt.filter2_idx = uninterpHash2b(pkt.sport, pkt.dport) % NUM_ENTRIES;
    pkt.filter3_idx = uninterpHash2c(pkt.sport, pkt.dport) % NUM_ENTRIES;
    pkt.member = (filter1[pkt.filter1_idx] && filter2[pkt.filter2_idx] &&
                  filter3[pkt.filter3_idx]);

    filter1[pkt.filter1_idx] = 1;
    filter2[pkt.filter2_idx] = 1;
    filter3[pkt.filter3_idx] = 1;
}
*/

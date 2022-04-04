#include "list.h"

#define TIME_MIN 10

/* These functions are uninterpreted, hence the no-op implementations */
extern "C" int uninterpHash2(int sport, int dport) { return -1000000; }

/**
 * The actual benchmark functions.
 * Note: We assume array accesses happen in the outside function (to work around
 * need for random-access to arrays). We further elide the modulo
 * operation away since none of the Domino atoms have modulo
 * as a valid operation.
 */
extern "C" List<int> stage0(int sport, int dport) {
    // pkt.id = hash2(pkt.sport, pkt.dport) % NUM_FLOWS;
    int id = uninterpHash2(sport, dport);

    List<int> out = newList<int>();
    out = listAppend(out, id);
    return out;
}

extern "C" List<int> stage1(int last_finish_pkt_id, int virtual_time) {
    /*
    if ((last_finish[pkt.id] > TIME_MIN) &&
        (pkt.virtual_time < last_finish[pkt.id]))
    */
    int member;
    if (last_finish_pkt_id > TIME_MIN) {
        if (virtual_time < last_finish_pkt_id) {
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

extern "C" List<int> stage2(int stage1_output, int pkt_id,
                            int last_finish_pkt_id, int length,
                            int virtual_time) {
    /*
    if ((last_finish[pkt.id] > TIME_MIN) &&
        (pkt.virtual_time < last_finish[pkt.id])) {
        pkt.start = last_finish[pkt.id];
        last_finish[pkt.id] += pkt.length;
    } else {
        pkt.start = pkt.virtual_time;
        last_finish[pkt.id] = pkt.virtual_time + pkt.length;
    }
    */
    int start;
    if (stage1_output > 0) {
        start = last_finish_pkt_id;
        last_finish_pkt_id += length;
    } else {
        start = virtual_time;
        last_finish_pkt_id = virtual_time + length;
    }

    List<int> out = newList<int>();
    out = listAppend(out, start);
    out = listAppend(out, last_finish_pkt_id);
    return out;
}

/*
struct Packet {
    int sport;
    int dport;
    int id;
    int start;
    int length;
    int virtual_time;
};

int last_finish[NUM_FLOWS] = {TIME_MIN};

void stfq(struct Packet pkt) {
    pkt.id = hash2(pkt.sport, pkt.dport) % NUM_FLOWS;

    if ((last_finish[pkt.id] > TIME_MIN) &&
        (pkt.virtual_time < last_finish[pkt.id])) {
        pkt.start = last_finish[pkt.id];
        last_finish[pkt.id] += pkt.length;
    } else {
        pkt.start = pkt.virtual_time;
        last_finish[pkt.id] = pkt.virtual_time + pkt.length;
    }
}
*/

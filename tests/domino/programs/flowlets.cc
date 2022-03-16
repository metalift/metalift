#include "list.h"

#define NUM_FLOWLETS 8000
#define THRESHOLD 10
#define NUM_HOPS 20

/* These functions are uninterpreted, hence the no-op implementations */
extern "C" int uninterpHash3(int sport, int dport) { return -1000000; }
extern "C" int uninterpHash2(int sport, int dport) { return -2000000; }
extern "C" int uninterpReadFilter1At(int idx) { return -10000001; }
extern "C" int uninterpReadFilter2At(int idx) { return -20000002; }
extern "C" int uninterpReadFilter3At(int idx) { return -30000003; }

/**
 * The actual benchmark functions.
 * Note: We assume array accesses are done in the outside function
 * (to work around need for random-access to arrays), either through
 * decomposition or by modelling an array access as an uninterpreted
 * function. We further elide the modulo operation away since none of
 * the Domino atoms have modulo as a valid operation.
 */
extern "C" List<int> stage0(int sport, int dport, int arrival) {
    /*
    pkt.new_hop = hash3(pkt.sport,
                      pkt.dport,
                      pkt.arrival)
                % NUM_HOPS;

    pkt.id  = hash2(pkt.sport,
                  pkt.dport)
            % NUM_FLOWLETS;
    */
    int pkt_new_hop = uninterpHash3(sport, dport);
    int pkt_id = uninterpHash2(sport, dport);

    List<int> out = newList<int>();
    out = listAppend(out, pkt_new_hop);
    out = listAppend(out, pkt_id);
    return out;
}

extern "C" List<int> stage1p1(int pkt_arrival, int last_time_pkt_id) {
    /*
    if (pkt.arrival -
        last_time[pkt.id] >
        THRESHOLD) {
        saved_hop[pkt.id] = pkt.new_hop;
    }
    */
    int cond_lhs = pkt_arrival - last_time_pkt_id;

    List<int> out = newList<int>();
    out = listAppend(out, cond_lhs);
    return out;
}

extern "C" List<int> stage1p2(int cond_lhs, int saved_hop_pkt_id,
                              int pkt_new_hop) {
    /*
    if (pkt.arrival -
        last_time[pkt.id] >
        THRESHOLD) {
        saved_hop[pkt.id] = pkt.new_hop;
    }
    */
    if (cond_lhs > THRESHOLD) {
        saved_hop_pkt_id = pkt_new_hop;
    } else {
        saved_hop_pkt_id = saved_hop_pkt_id;
    }

    List<int> out = newList<int>();
    out = listAppend(out, saved_hop_pkt_id);
    return out;
}

extern "C" List<int> stage2(int pkt_arrival, int saved_hop_pkt_id) {
    /*
    last_time[pkt.id] = pkt.arrival;
    pkt.next_hop = saved_hop[pkt.id];
    */
    int last_time_pkt_id = pkt_arrival;
    int pkt_next_hop = saved_hop_pkt_id;

    List<int> out = newList<int>();
    out = listAppend(out, last_time_pkt_id);
    out = listAppend(out, pkt_next_hop);
    return out;
}

/*
struct Packet {
  int sport;
  int dport;
  int new_hop;
  int arrival;
  int next_hop;
  int id; // array index
};

int last_time [NUM_FLOWLETS] = {0};
int saved_hop [NUM_FLOWLETS] = {0};

void flowlet(struct Packet pkt) {
  pkt.new_hop = hash3(pkt.sport,
                      pkt.dport,
                      pkt.arrival)
                % NUM_HOPS;

  pkt.id  = hash2(pkt.sport,
                  pkt.dport)
            % NUM_FLOWLETS;

  if (pkt.arrival -
      last_time[pkt.id] >
      THRESHOLD) {
    saved_hop[pkt.id] = pkt.new_hop;
  }

  last_time[pkt.id] = pkt.arrival;
  pkt.next_hop = saved_hop[pkt.id];
}
*/

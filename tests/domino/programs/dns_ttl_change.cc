#include "list.h"

/** Assumes seen_pid => seen[p.id], last_ttl_pid => last_ttl[p.id]
    ttl_change_pid => ttl_change[p.id] and returns their new values */
extern "C" List<int> test(int sport, int rdata, int ttl, int id, int seen_pid,
                          int last_ttl_pid, int ttl_change_pid) {
    id = rdata;
    if (seen_pid == 0) {
        seen_pid = 1;
        last_ttl_pid = ttl;
        ttl_change_pid = 0;
    } else {
        if (last_ttl_pid != ttl) {
            last_ttl_pid = ttl;
            ttl_change_pid += 1;
        }
    }

    List<int> out = newList<int>();
    // out = listAppend(out, id);
    out = listAppend(out, seen_pid);
    out = listAppend(out, last_ttl_pid);
    out = listAppend(out, ttl_change_pid);
    return out;
}

/*
struct Packet {
    int sport;
    int rdata;
    int ttl;
    int id;
};

#define NUM_RECORDS 10000

int seen[NUM_RECORDS] = {0};
int last_ttl[NUM_RECORDS] = {0};
int ttl_change[NUM_RECORDS] = {0};

void func(struct Packet p) {
    p.id = p.rdata;
    if (seen[p.id] == 0) {
        seen[p.id] = 1;
        last_ttl[p.id] = p.ttl;
        ttl_change[p.id] = 0;
    } else {
        if (last_ttl[p.id] != p.ttl) {
            last_ttl[p.id] = p.ttl;
            ttl_change[p.id] += 1;
        }
    }
}
*/

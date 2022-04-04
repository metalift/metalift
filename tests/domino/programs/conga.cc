#include "list.h"

/* Assumes pkt_src_mod_256 is p.src % 256 since Domino does not have modulo. */
extern "C" List<int> stage0(int pkt_src, int pkt_src_mod_256) {
    /*
    p.best_path_util_idx = p.src < 0 ? 0 : p.src % 256;
    p.best_path_idx = p.src < 0 ? 0 : p.src % 256;
    */
    int best_path_util_idx;
    int best_path_idx;

    if (pkt_src < 0) {
        best_path_util_idx = 0;
    } else {
        best_path_util_idx = pkt_src_mod_256;
    }

    if (pkt_src < 0) {
        best_path_idx = 0;
    } else {
        best_path_idx = pkt_src_mod_256;
    }

    List<int> out = newList<int>();
    out = listAppend(out, best_path_util_idx);
    out = listAppend(out, best_path_idx);
    return out;
}

extern "C" List<int> stage1p1(int pkt_util,
                              int best_path_util_best_path_util_idx,
                              int pkt_path_id, int best_path_best_path_idx) {
    /*
    if (p.util < best_path_util[p.best_path_util_idx]) {
        best_path_util[p.best_path_util_idx] = p.util;
        best_path[p.best_path_idx] = p.path_id;
    } else if (p.path_id == best_path[p.best_path_idx]) {
        best_path_util[p.best_path_util_idx] = p.util;
        // TODO: I guess we aren't switching to another path in
        // case the utilization on the best path went up.
    }
    */
    if (pkt_util < best_path_util_best_path_util_idx) {
        best_path_util_best_path_util_idx = pkt_util;
    } else {
        if (pkt_path_id == best_path_best_path_idx) {
            best_path_util_best_path_util_idx = pkt_util;
        } else {
            best_path_util_best_path_util_idx =
                best_path_util_best_path_util_idx;
        }
    }

    List<int> out = newList<int>();
    out = listAppend(out, best_path_util_best_path_util_idx);
    return out;
}

extern "C" List<int> stage1p2(int pkt_util,
                              int best_path_util_best_path_util_idx,
                              int pkt_path_id, int best_path_best_path_idx) {
    /*
    if (p.util < best_path_util[p.best_path_util_idx]) {
        best_path_util[p.best_path_util_idx] = p.util;
        best_path[p.best_path_idx] = p.path_id;
    } else if (p.path_id == best_path[p.best_path_idx]) {
        best_path_util[p.best_path_util_idx] = p.util;
        // TODO: I guess we aren't switching to another path in
        // case the utilization on the best path went up.
    }
    */
    if (pkt_util < best_path_util_best_path_util_idx) {
        best_path_best_path_idx = pkt_path_id;
    } else {
        best_path_best_path_idx = best_path_best_path_idx;
    }

    List<int> out = newList<int>();
    out = listAppend(out, best_path_best_path_idx);
    return out;
}

/*
// This is a packet reflected back from a destination leaf (d)
// (confusingly called the src field in the packet)
// informing the source leaf (s) what the max util (util) on
// a particular path (path_id) to d is.
// This helps s maintain at any point, the max. util on the best path to d
// and the id of the path to d as well.
struct Packet {
    int util;
    int path_id;
    int src;
    int best_path_util_idx;
    int best_path_idx;
};

int best_path_util[256] = {
    100};  // Utilization information for each destination, Initially at 100%
           // for everyone.
int best_path[256] = {-1};  // Next hop / path information for each destination

void func(struct Packet p) {
    p.best_path_util_idx = p.src < 0 ? 0 : p.src % 256;
    p.best_path_idx = p.src < 0 ? 0 : p.src % 256;
    if (p.util < best_path_util[p.best_path_util_idx]) {
        best_path_util[p.best_path_util_idx] = p.util;
        best_path[p.best_path_idx] = p.path_id;
    } else if (p.path_id == best_path[p.best_path_idx]) {
        best_path_util[p.best_path_util_idx] = p.util;
        // TODO: I guess we aren't switching to another path in
        // case the utilization on the best path went up.
    }
}

// Also, CONGA has multiple transactions, while we are only dealing with
// the hardest of these transactions here.
*/

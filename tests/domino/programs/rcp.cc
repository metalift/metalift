#include "list.h"
#define MAX_ALLOWABLE_RTT 30

extern "C" List<int> test(int size_bytes, int rtt, int _input_traffic_Bytes,
                          int _sum_rtt_Tr, int _num_pkts_with_rtt) {
    _input_traffic_Bytes += size_bytes;
    if (rtt < MAX_ALLOWABLE_RTT) {
        _sum_rtt_Tr += rtt;
        _num_pkts_with_rtt += 1;
    }

    List<int> out = newList<int>();
    out = listAppend(out, _input_traffic_Bytes);
    out = listAppend(out, _sum_rtt_Tr);
    out = listAppend(out, _num_pkts_with_rtt);
    return out;
}

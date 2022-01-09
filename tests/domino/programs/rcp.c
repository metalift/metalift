#define MAX_ALLOWABLE_RTT 30

// // Total number of bytes seen so far.
// int input_traffic_Bytes = 0;

// // Sum of rtt so far
// int sum_rtt_Tr = 0;

// // Number of packets with a valid RTT
// int num_pkts_with_rtt = 0;

// struct Packet
// {
//     int size_bytes;
//     int rtt;
// };

int func(int size_bytes, int rtt, int _input_traffic_Bytes, int _sum_rtt_Tr, int _num_pkts_with_rtt) {
    _input_traffic_Bytes += size_bytes;
    if (rtt < MAX_ALLOWABLE_RTT)
    {
        _sum_rtt_Tr += rtt;
        _num_pkts_with_rtt += 1;
    }

    int sum = 0;
    sum = size_bytes + rtt + _input_traffic_Bytes + _sum_rtt_Tr + _num_pkts_with_rtt; // (knownbug: need sum = 0 and this assignment on separate lines)
    return sum;
}

#define MAX_ALLOWABLE_RTT 30

// Total number of bytes seen so far.
int input_traffic_Bytes = 0;

// Sum of rtt so far
int sum_rtt_Tr = 0;

// Number of packets with a valid RTT
int num_pkts_with_rtt = 0;

struct Packet
{
    int size_bytes;
    int rtt;
};

void func(struct Packet pkt)
{
    input_traffic_Bytes += pkt.size_bytes;
    if (pkt.rtt < MAX_ALLOWABLE_RTT)
    {
        sum_rtt_Tr += pkt.rtt;
        num_pkts_with_rtt += 1;
    }
}

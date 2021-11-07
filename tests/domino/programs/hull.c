#define DRAIN_RATE 10
#define ECN_THRESH 20

/* int counter = ECN_THRESH;
int last_time = 0; */

/* struct Packet
{
    int bytes;
    int time;
    int mark;
}; */

int test(int counter, int last_time, int bytes, int time, int mark)
{
    // Decrement counter according to drain rate
    // counter = counter - (time - last_time) * DRAIN_RATE;
    // if (counter < 0)
    //     counter = 0;

    // // Increment counter
    // counter += bytes;

    // // If we are above the ECN_THRESH, mark
    // if (counter > ECN_THRESH)
    //     mark = 1;

    // Store last time
    last_time = time;

    return bytes + mark + time + counter + last_time;
}

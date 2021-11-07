#define ALPHA 5
#define GAMMA 2
#define CAPACITY 10
#define BUFFER 3

struct Packet
{
    int bytes;
    int time;
    int mark;
    int min;
    int max;
    int max_vq;
};

int vq = 0;
int capacity = 0;
int last_time = 0;

void func(struct Packet p)
{
    // Update virtual queue size
    vq = ((vq - capacity * (p.time - last_time)) < 0) ? 0 : (vq - capacity * (p.time - last_time));

    // Mark or drop packet in real queue
    if (vq + p.bytes > BUFFER)
    {
        p.mark = 1;
    }
    else
    {
        vq = vq + p.bytes;
    }

    // Update virtual capacity
    p.min = ((capacity + ALPHA * GAMMA * CAPACITY * (p.time - last_time)) < CAPACITY) ? (capacity + ALPHA * GAMMA * CAPACITY * (p.time - last_time)) : CAPACITY;
    p.max = (p.min - ALPHA * p.bytes < 0) ? 0 : p.min - ALPHA * p.bytes;
    capacity = p.max;

    last_time = p.time;
}

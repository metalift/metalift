struct Packet
{
    int sport;
    int rdata;
    int ttl;
    int id;
};

#define NUM_RECORDS 10000

int seen[NUM_RECORDS] = {0};
int last_ttl[NUM_RECORDS] = {0};
int ttl_change[NUM_RECORDS] = {0};

void func(struct Packet p)
{
    p.id = p.rdata;
    if (seen[p.id] == 0)
    {
        seen[p.id] = 1;
        last_ttl[p.id] = p.ttl;
        ttl_change[p.id] = 0;
    }
    else
    {
        if (last_ttl[p.id] != p.ttl)
        {
            last_ttl[p.id] = p.ttl;
            ttl_change[p.id] += 1;
        }
    }
}

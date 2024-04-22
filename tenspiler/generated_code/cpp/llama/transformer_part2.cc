#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<float> transformer_part2(
    int token_position,
    int head,
    int head_size,
    vector<vector<float>> key_cache_layer,
    vector<float> attention
) {
    vector<float> xb;
    for (int i = 0; i < head_size; i++) {
        float curr = 0;
        for (int timestep = 0; timestep <= token_position; timestep++) {
            curr += attention[timestep] * key_cache_layer[timestep][head * head_size + i];
        }
        xb.push_back(curr);
    }
    return xb;
}

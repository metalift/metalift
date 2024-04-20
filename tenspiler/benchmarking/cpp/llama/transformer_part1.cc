#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<float> transformer_part1(
    int token_position,
    int head,
    int head_size,
    vector<vector<float>> key_cache_layer,
    vector<float> q
) {
    vector<float> attention;
    for (int timestep = 0; timestep < token_position; timestep++) {
        float score = 0;
        for (int i = 0; i < head_size; ++i) {
            score += q[head * head_size + i] * key_cache_layer[timestep][head * head_size + i];
        }
        score /= sqrt(head_size * 1.0);
        attention.push_back(score);
    }
    return attention;
}

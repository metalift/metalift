#include <vector>
using namespace std;

vector<int> transformer_part2(
    int token_position,
    int head,
    int head_size,
    vector<vector<int>> key_cache_layer,
    vector<int> attention
) {
    vector<int> xb;
    for (int i = 0; i < head_size; i++) {
        int curr = 0;
        for (int timestep = 0; timestep <= token_position; timestep++) {
            curr += attention[timestep] * key_cache_layer[timestep][head * head_size + i];
        }
        xb.push_back(curr);
    }
    return xb;
}
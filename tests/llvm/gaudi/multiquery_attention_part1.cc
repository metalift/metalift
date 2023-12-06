#include <vector>
using namespace std;

int test_exp(int x) { return x; }

vector<int> multiquery_attention_part1(
    int token_position,
    int head,
    int head_size,
    vector<vector<int>> key_cache_layer,
    vector<int> q
) {
    vector<int> attention;
    for (int timestep = 0; timestep < token_position; timestep++) {
        int score = 0;
        for (int i = 0; i < head_size; ++i) {
            score += q[head * head_size + i] * key_cache_layer[timestep][head * head_size + 1];
        }
        // score = score / test_exp(score * 1);
        attention.push_back(score);
    }
    return attention;
}

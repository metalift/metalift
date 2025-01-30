#include <vector>
using namespace std;

int integer_sqrt(int x) { return x; }

vector<int> transformer_part1(
    int token_position,
    int head1,
    int head_size,
    vector<vector<int>> key_cache_layer,
    vector<int> q
) {
    vector<int> attention;
    for (int timestep = 0; timestep < token_position; timestep++) {
        int score = 0;
        for (int i = 0; i < head_size; ++i) {
            score += q[head1 * head_size + i] * key_cache_layer[timestep][head1 * head_size + i];
        }
        score /= integer_sqrt(head_size * 1);
        attention.push_back(score);
    }
    return attention;
}

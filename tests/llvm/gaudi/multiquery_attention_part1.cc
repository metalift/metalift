#include <vector>
using namespace std;

int integer_exp(int x) { return x; }

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
            score += q[head * head_size + i] * key_cache_layer[timestep][head * head_size + i];
        }
        // score = score / integer_exp(score * 1);
        attention.push_back(score);
    }
    return attention;
}
// def multiquery_attention_part1_ps(token_position head head_size key_cache_layer q multiquery_attention_part1_rv)
// list_eq(multiquery_attention_part1_rv, matrix_vec_mul(list_col_slice_with_length(list_take(key_cache_layer, token_position), (head * head_size), head_size), list_slice_with_length(q, (head * head_size), head_size)))

// def map_int_to_int(int_x)
// integer_exp(int_x)
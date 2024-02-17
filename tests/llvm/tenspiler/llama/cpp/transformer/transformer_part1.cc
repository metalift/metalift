#include <vector>
using namespace std;

int integer_sqrt(int x) { return x; }

vector<int> transformer_part1(
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
        score /= integer_sqrt(head_size * 1);
        attention.push_back(score);
    }
    return attention;
}
// def transformer_part1_ps(token_position head head_size key_cache_layer q transformer_part1_rv):
    // computed_vec = matrix_vec_mul(list_list_col_slice_with_length(list_take(key_cache_layer, token_position), (head * head_size), head_size), list_slice_with_length(q, (head * head_size), head_size))

    // return list_eq(transformer_part1_rv, vec_scalar_div(map_int_to_int(head_size * 1), computed_vec))

// def map_int_to_int(int_x)
// integer_sqrt(int_x)

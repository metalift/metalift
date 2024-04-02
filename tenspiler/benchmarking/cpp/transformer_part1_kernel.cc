#include <iostream>
#include <vector>
#include <chrono>
#include <tuple>

#include "utils.h"
#include <cmath>

using namespace std;
using namespace std::chrono;

std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time;

vector<float>transformer_part1_kernel(
    int token_position,
    int head,
    int head_size,
    vector<vector<float>> key_cache_layer,
    vector<float> q
) {
    vector<float> attention;
    start_time = high_resolution_clock::now();
    for (int timestep = 0; timestep < token_position; timestep++) {
        float score = 0;
        for (int i = 0; i < head_size; ++i) {
            score += q[head * head_size + i] * key_cache_layer[timestep][head * head_size + i];
        }
        score /= sqrt(head_size * 1.0);
        attention.push_back(score);
    }
    end_time = high_resolution_clock::now();
    return attention;
}

int main() {
    setup_timer(false, false, true);

    vector<long long> times;
    size_t count = k_weights.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            vector<vector<float>> k_matrix = k_weights[j];

            int token_position = k_matrix.size() - 1;
            int num_head = 32;
            int head = static_cast<int>(random_float() * num_head);
            int head_size = k_matrix.size() / num_head;


            vector<float> q = flatten(q_weights[j]);

            transformer_part1_kernel(token_position, head, head_size, k_matrix, q);
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);

    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}

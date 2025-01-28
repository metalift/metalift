#include <iostream>
#include <vector>
#include <chrono>
#include <stdio.h>
#include <stdlib.h>

#include "utils.h"

using namespace std;
using namespace std::chrono;

std::chrono::time_point<std::chrono::high_resolution_clock> start_time_k;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time_k;
#include <cmath>

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


vector<float> transformer_part2(
    int token_position,
    int head,
    int head_size,
    vector<vector<float>> key_cache_layer,
    vector<float> attention
) {
    start_time_k = high_resolution_clock::now();
    vector<float> xb;
    for (int i = 0; i < head_size; i++) {
        float curr = 0;
        for (int timestep = 0; timestep <= token_position; timestep++) {
            curr += attention[timestep] * key_cache_layer[timestep][head * head_size + i];
        }
        xb.push_back(curr);
    }
    end_time_k = high_resolution_clock::now();
    return xb;
}


int main() {
    setup_timer(false, false, true);

    vector<long long> times;
    vector<long long> times_k;
    size_t count = k_weights.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        long long time_k = 0;
        for (int j = 0; j < count; j++) {
            vector<vector<float>> k_matrix = k_weights[j];

            int token_position = k_matrix.size() - 1;
            int num_head = 32;
            int head = static_cast<int>(random_float() * num_head);
            int head_size = k_matrix.size() / num_head;


            vector<float> q = flatten(q_weights[j]);

            vector<float> attention = transformer_part1(token_position, head, head_size, k_matrix, q);
            attention.push_back(0);

            auto start_time = high_resolution_clock::now();
            transformer_part2(token_position, head, head_size, k_matrix, attention);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();

        }
        cout << "transformer_part2" << endl;
        times.push_back(time);
        times_k.push_back(time_k);
    }

    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;
    return 0;
}

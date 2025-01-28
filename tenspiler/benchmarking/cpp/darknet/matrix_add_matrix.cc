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


vector<vector<int32_t>> matrix_add_matrix(vector<vector<int32_t>> from_matrix, vector<vector<int32_t>> to_matrix)
{
    start_time_k = high_resolution_clock::now();
    int i, j;
    vector<vector<int32_t>> out;
    for (i = 0; i < from_matrix.size(); ++i) {
        vector<int32_t> row_vec;
        for (j = 0; j < from_matrix[0].size(); ++j) {
            row_vec.push_back(from_matrix[i][j] + to_matrix[i][j]);
        }
        out.push_back(row_vec);
    }
    end_time_k = high_resolution_clock::now();
    return out;
}

int main() {
    srand(1);
    fn = glob("./data/", ".*\\.jpeg$");

    vector<long long> times;
    vector<long long> times_k;

    size_t count = fn.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        long long time_k = 0;
        for (int j = 0; j < count; j++) {
            std::array<vector<vector<int32_t>>,2> res = get_base_active_int(j);
            vector<vector<int32_t>> base = res[0];
            vector<vector<int32_t>> active = res[1];

            auto start_time = high_resolution_clock::now();
            matrix_add_matrix(base, active);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();

        }
        times.push_back(time);
        times_k.push_back(time_k);
    }
    cout << "matrix_add_matrix" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;

}

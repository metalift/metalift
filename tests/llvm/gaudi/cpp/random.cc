#include <bits/stdc++.h>

#include <vector>
using namespace std;

float random_float() {
    return (float)(rand()) / (float)(RAND_MAX);
}

vector<vector<float>> random_matrix(int m = 512, int n = 512) {
    vector<vector<float>> matrix(m, vector<float>(n, 0));
    for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
            matrix[i][j] = random_float();
        }
    }
    return matrix;
}

vector<float> random_vector(int m = 512) {
    vector<float> vec(m, 0);
    for (int i = 0; i < m; i++) {
        vec[i] = random_float();
    }
    return vec;
}

double average(std::vector<long long> v) {
    if(v.empty()){
        return 0;
    }

    auto const count = static_cast<double>(v.size());
    return std::reduce(v.begin(), v.end()) / count;
}

double stdiv(std::vector<long long> v) {
    long long sum = std::accumulate(v.begin(), v.end(), 0.0);
    double mean = sum / static_cast<double>(v.size());

    std::vector<double> diff(v.size());
    std::transform(v.begin(), v.end(), diff.begin(),
                std::bind2nd(std::minus<double>(), mean));
    double sq_sum = std::inner_product(diff.begin(), diff.end(), diff.begin(), 0.0);
    double stdev = std::sqrt(sq_sum / v.size());
    return stdev;
}
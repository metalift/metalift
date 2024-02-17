#include <bits/stdc++.h>

#include <vector>
#include <iostream>
#include <chrono>

#include "utils.h"
#include <cassert>

using namespace std;
using namespace std::chrono;

#include <opencv2/opencv.hpp>
using namespace cv;

static vector<cv::String> fn;


float random_float() {
    return (float)(rand()) / (float)(RAND_MAX);
}

float random_float_grayscale() {
    return static_cast<float>(rand()) / (static_cast<float>(RAND_MAX / 255.0));
}

vector<vector<float>> random_matrix(int m, int n) {
    vector<vector<float>> matrix(m, vector<float>(n, 0));
    for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
            matrix[i][j] = random_float_grayscale();
        }
    }
    return matrix;
}

vector<float> random_vector(int m) {
    vector<float> vec(m, 0);
    for (int i = 0; i < m; i++) {
        vec[i] = random_float_grayscale();
    }
    return vec;
}

std::array<vector<vector<float>>,2> get_base_active(int i) {
    Mat img = imread(fn[i], IMREAD_GRAYSCALE);
    //assert dim 2
    assert(img.dims == 2);
    vector<vector<float> > base(img.rows, vector<float>(img.cols));

    for(int i=0; i < img.rows; ++i) {
        for(int j=0; j < img.cols; ++j){
            base.at(i).at(j) = img.at<float>(i, j);
        }
    }
    vector<vector<float> > active = random_matrix(img.rows, img.cols);

    std::array<vector<vector<float>>,2> res;
    res[0] = base;
    res[1] = active;
    return res;
}

std::vector<float> flatten(const std::vector<std::vector<float>>& nested) {
    std::vector<float> flat;

    for (const auto& inner : nested) {
        flat.insert(flat.end(), inner.begin(), inner.end());
    }

    return flat;
}

void mat_timer(vector<vector<float>> (*func)(vector<vector<float>>, vector<vector<float>>)) {
    glob("./data/*.jpeg", fn, false);

    vector<long long> times;
    size_t count = fn.size();
    for (int i = 0; i < 5; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            std::array<vector<vector<float>>,2> res = get_base_active(j);
            vector<vector<float>> base = res[0];
            vector<vector<float>> active = res[1];
            auto start_time = high_resolution_clock::now();
            func(base, active);
            auto end_time = high_resolution_clock::now();
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) << " microseconds +/-" << stdiv(times) << endl;
}

void vec_timer(vector<float> (*func)(vector<float>, vector<float>, float)) {
    glob("./data/*.jpeg", fn, false);

    vector<long long> times;
    size_t count = fn.size();
    for (int i = 0; i < 5; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            std::array<vector<vector<float>>,2> res = get_base_active(j);
            vector<vector<float>> base = res[0];
            vector<float> base_f = flatten(base);
            vector<vector<float>> active = res[1];
            vector<float> active_f = flatten(active);
            float opacity = random_float();
            auto start_time = high_resolution_clock::now();
            func(base_f, active_f, opacity);
            auto end_time = high_resolution_clock::now();
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) << " microseconds +/-" << stdiv(times) << endl;
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

#include <bits/stdc++.h>

#include <vector>
#include <iostream>
#include <chrono>

#include "utils.h"
#include <cassert>
#include <string>
#include <dirent.h>
#include <sys/types.h>
#include <regex>

using namespace std;
using namespace std::chrono;

#include <opencv2/opencv.hpp>
#include <opencv2/highgui/highgui.hpp>
#include <opencv2/highgui/highgui_c.h>
using namespace cv;
#include "H5Cpp.h"
#include <H5public.h>

vector<cv::String> fn;

vector<vector<vector<float>>> weights;
vector<vector<vector<float>>> w_input;
vector<vector<vector<float>>> attn_weights;
vector<vector<float>> aw_input;
vector<vector<vector<float>>> q_weights;
vector<vector<vector<float>>> k_weights;

std::vector<std::string> glob(const std::string& directory, const std::string& pattern) {
    std::vector<std::string> matches;
    std::regex re(pattern);

    DIR* dir;
    struct dirent* ent;
    if ((dir = opendir(directory.c_str())) != nullptr) {
        while ((ent = readdir(dir)) != nullptr) {
            std::string fileName = ent->d_name;
            if (std::regex_match(fileName, re)) {
                matches.push_back(directory + "/" + fileName);
            }
        }
        closedir(dir);
    } else {
        perror("Unable to open directory");
    }

    return matches;
}

float random_float() {
    return (float)(rand()) / (float)(RAND_MAX);
}

uint8_t random_grayscale() {
    return static_cast<uint8_t>(static_cast<float>(rand()) / (static_cast<float>(RAND_MAX / 255.0)));
}

vector<vector<float>> random_matrix(int m, int n) {
    vector<vector<float>> matrix(m, vector<float>(n, 0));
    for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
            matrix[i][j] = random_float();
        }
    }
    return matrix;
}

vector<vector<uint8_t>> random_matrix_grayscale(int m, int n) {
    vector<vector<uint8_t>> matrix(m, vector<uint8_t>(n, 0));
    for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
            matrix[i][j] = random_grayscale();
        }
    }
    return matrix;
}

vector<float> random_vector(int m) {
    vector<float> vec(m, 0);
    for (int i = 0; i < m; i++) {
        vec[i] = random_float();
    }
    return vec;
}

std::array<vector<vector<uint8_t>>,2> get_base_active(int i) {
    IplImage* img_c = cvLoadImage(fn[i].c_str(), CV_LOAD_IMAGE_GRAYSCALE);
    cv::Mat img(img_c, true);
    //assert dim 2
    assert(img.dims == 2);
    vector<vector<uint8_t> > base(img.rows, vector<uint8_t>(img.cols));

    for(int i=0; i < img.rows; ++i) {
        for(int j=0; j < img.cols; ++j){
            base.at(i).at(j) = static_cast<uint8_t>(img.at<uchar>(i, j));
        }
    }
    cvReleaseImage(&img_c);
    vector<vector<uint8_t> > active = random_matrix_grayscale(img.rows, img.cols);

    std::array<vector<vector<uint8_t>>,2> res;
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

std::vector<uint8_t> flatten_int(const std::vector<std::vector<uint8_t>>& nested) {
    std::vector<uint8_t> flat;

    for (const auto& inner : nested) {
        flat.insert(flat.end(), inner.begin(), inner.end());
    }

    return flat;
}

void mat_timer(vector<vector<uint8_t>> (*func)(vector<vector<uint8_t>>, vector<vector<uint8_t>>)) {
    srand(1);
    fn = glob("./data", ".*\\.jpeg$");

    vector<long long> times;
    size_t count = fn.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            std::array<vector<vector<uint8_t>>,2> res = get_base_active(j);
            vector<vector<uint8_t>> base = res[0];
            vector<vector<uint8_t>> active = res[1];
            auto start_time = high_resolution_clock::now();
            func(base, active);
            auto end_time = high_resolution_clock::now();
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }

    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
}

void mat_timer_float(vector<vector<float>> (*func)(vector<vector<float>>, vector<vector<float>>, float)) {
    srand(1);
    fn = glob("./data", ".*\\.jpeg$");

    vector<long long> times;
    size_t count = fn.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            std::array<vector<vector<uint8_t>>,2> res = get_base_active(j);
            vector<vector<uint8_t>> base_int = res[0];
            vector<vector<uint8_t>> active_int = res[1];

            vector<vector<float>> base(base_int.size(), vector<float>());

            for (size_t i = 0; i < base_int.size(); ++i) {
                base[i].resize(base_int[i].size());
                for (size_t j = 0; j < base_int[i].size(); ++j) {
                    base[i][j] = static_cast<float>(base_int[i][j]);
                }
            }

            vector<vector<float>> active(active_int.size(), vector<float>());

            for (size_t i = 0; i < active_int.size(); ++i) {
                active[i].resize(active_int[i].size());
                for (size_t j = 0; j < active_int[i].size(); ++j) {
                    active[i][j] = static_cast<float>(active_int[i][j]);
                }
            }

            float opacity = random_float();

            auto start_time = high_resolution_clock::now();
            func(base, active, opacity);
            auto end_time = high_resolution_clock::now();
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }

    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
}

void vec_timer_float(vector<float> (*func)(vector<float>, vector<float>, float)) {
    srand(1);
    fn = glob("./data", ".*\\.jpeg$");

    vector<long long> times;
    size_t count = fn.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            std::array<vector<vector<uint8_t>>,2> res = get_base_active(j);
            vector<vector<uint8_t>> base_int = res[0];
            vector<vector<uint8_t>> active_int = res[1];
            vector<vector<float>> base(base_int.size(), vector<float>());

            for (size_t i = 0; i < base_int.size(); ++i) {
                base[i].resize(base_int[i].size());
                for (size_t j = 0; j < base_int[i].size(); ++j) {
                    base[i][j] = static_cast<float>(base_int[i][j]);
                }
            }

            vector<vector<float>> active(active_int.size(), vector<float>());

            for (size_t i = 0; i < active_int.size(); ++i) {
                active[i].resize(active_int[i].size());
                for (size_t j = 0; j < active_int[i].size(); ++j) {
                    active[i][j] = static_cast<float>(active_int[i][j]);
                }
            }

            vector<float> base_f = flatten(base);
            vector<float> active_f = flatten(active);
            float opacity = random_float();
            auto start_time = high_resolution_clock::now();
            func(base_f, active_f, opacity);
            auto end_time = high_resolution_clock::now();
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }

    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
}

void vec_timer_int(vector<uint8_t> (*func)(vector<uint8_t>, vector<uint8_t>, uint8_t)) {
    srand(1);
    fn = glob("./data", ".*\\.jpeg$");

    vector<long long> times;
    size_t count = fn.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            std::array<vector<vector<uint8_t>>,2> res = get_base_active(j);
            vector<vector<uint8_t>> base = res[0];
            vector<uint8_t> base_f = flatten_int(base);
            vector<vector<uint8_t>> active = res[1];
            vector<uint8_t> active_f = flatten_int(active);
            uint8_t opacity = static_cast<uint8_t>(random_float());
            auto start_time = high_resolution_clock::now();
            func(base_f, active_f, opacity);
            auto end_time = high_resolution_clock::now();
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
}

void setup_timer(bool needWeights, bool needAttnWeights, bool needProjWeights) {
    srand(1);
    // H5::H5File file("/tier2/ucb/metalift/vicuna_weight.h5", H5F_ACC_RDONLY);
    H5::H5File file("/homes/colinc9/benchmarks/vicuna_weight_7b.h5", H5F_ACC_RDONLY);

    H5::Group root = file.openGroup("/");

    hsize_t num_obj = root.getNumObjs();
    for (hsize_t i = 0; i < num_obj; i++) {
        H5std_string obj_name = root.getObjnameByIdx(i);

        if (obj_name.find("model") == std::string::npos || obj_name.find("embed_tokens") != std::string::npos || obj_name.find("layernorm") != std::string::npos) {
            continue;
        }

        if (!needWeights && obj_name.find("attn") == std::string::npos) {
            continue;
        }

        H5::DataSet dataset = root.openDataSet(obj_name);
        H5::DataSpace dataspace = dataset.getSpace();

        hsize_t dims_out[2];
        dataspace.getSimpleExtentDims(dims_out, NULL);

        std::vector<float> data(dims_out[0] * dims_out[1]);
        dataset.read(data.data(), H5::PredType::NATIVE_FLOAT);

        std::vector<std::vector<float>> data2D(dims_out[0], std::vector<float>(dims_out[1]));
        for (int i = 0; i < dims_out[0]; ++i) {
            for (int j = 0; j < dims_out[1]; ++j) {
                data2D[i][j] = data[i * dims_out[1] + j];
            }
        }

        if (needWeights) {
            weights.push_back(data2D);
            w_input.push_back(random_matrix(dims_out[0], dims_out[1]));
        }

        if (obj_name.find("attn") != std::string::npos) {
            if (needAttnWeights) {
                attn_weights.push_back(data2D);
                aw_input.push_back(random_vector(dims_out[1]));
            }
            if (needProjWeights) {
                if (obj_name.find("q_proj") != std::string::npos) {
                    q_weights.push_back(data2D);
                }
                if (obj_name.find("k_proj") != std::string::npos) {
                    k_weights.push_back(data2D);
                }
            }
        }

    }
    file.close();
}

double average(std::vector<long long> v) {
    if(v.empty()){
        return 0;
    }

    auto const count = static_cast<double>(v.size());
    return std::accumulate(v.begin(), v.end(), 0.0) / count;
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

#include <bits/stdc++.h>

#include <vector>
using namespace std;

#include <opencv2/opencv.hpp>
using namespace cv;

extern vector<cv::String> fn;

extern vector<vector<vector<float>>> weights;
extern vector<vector<vector<float>>> w_input;

extern vector<vector<vector<float>>> attn_weights;
extern vector<vector<float>> aw_input;

extern vector<vector<vector<float>>> q_weights;
extern vector<vector<vector<float>>> k_weights;

std::array<vector<vector<uint8_t>>,2> get_base_active(int i);

void mat_timer(vector<vector<uint8_t>> (*func)(vector<vector<uint8_t>>, vector<vector<uint8_t>>));
void mat_timer_float(vector<vector<float>> (*func)(vector<vector<float>>, vector<vector<float>>, float));
void vec_timer_int(vector<uint8_t> (*func)(vector<uint8_t>, vector<uint8_t>, uint8_t));
void vec_timer_float(vector<float> (*func)(vector<float>, vector<float>, float));
void setup_timer(bool, bool, bool);

float random_float();
uint8_t random_grayscale();
vector<vector<float>> random_matrix(int m, int n) ;
vector<vector<uint8_t>> random_matrix_grayscale(int m, int n);
vector<float> random_vector(int m);

std::vector<float> flatten(const std::vector<std::vector<float>>& nested);
std::vector<uint8_t> flatten_int(const std::vector<std::vector<uint8_t>>& nested);

std::vector<std::string> glob(const std::string& directory, const std::string& pattern);

double average(std::vector<long long> v);
double stdiv(std::vector<long long> v);

std::vector<uint8_t> flatten_int(const std::vector<std::vector<uint8_t>>& nested);
std::vector<float> flatten(const std::vector<std::vector<float>>& nested);

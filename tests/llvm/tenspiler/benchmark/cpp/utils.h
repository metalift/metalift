#include <bits/stdc++.h>

#include <vector>
using namespace std;

#include <opencv2/opencv.hpp>
using namespace cv;

vector<vector<float>> random_matrix(int m = 512, int n = 512);
vector<float> random_vector(int n = 512);
float random_float();

std::array<vector<vector<float>>,2> get_base_active();

void mat_timer(vector<vector<float>> (*func)(vector<vector<float>>, vector<vector<float>>));
void vec_timer(vector<float> (*func)(vector<float>, vector<float>, float));

double average(std::vector<long long> v);
double stdiv(std::vector<long long> v);

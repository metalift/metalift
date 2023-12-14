#include <bits/stdc++.h>

#include <vector>
using namespace std;

float random_float() {
    return (float)(rand()) / (float)(RAND_MAX);
}

vector<vector<float>> random_matrix(int m = 512, int n = 512) {
    vector<vector<float>> matrix(512, vector<float>(512, 0));
    for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
            matrix[i][j] = random_float();
        }
    }
    return matrix;
}
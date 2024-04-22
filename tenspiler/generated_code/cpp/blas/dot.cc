#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

int32_t dot(vector<int32_t> a, vector<int32_t> b, int n) {
  int32_t sum = 0;
  for (int i = 0; i < n; ++i) {
    sum += a[i] * b[i];
  }
  return sum;
}

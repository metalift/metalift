#include <vector>
using namespace std;

int dot(vector<int> a, vector<int> b, int n) {
  int sum = 0;
  for (int i = 0; i < n; ++i) {
    sum += a[i] * b[i];
  }
  return sum;
}

// reduce_sum(vec_elemwise_mul(vec_slice(a, 0, n), vec_slice(b, 0, n)))

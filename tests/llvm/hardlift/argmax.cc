#include <vector>
using namespace std;

int argmax(vector<int> values) {
    int max_i = 0;
    int max_value = values[0];
    for (int i = 1; i < values.size(); ++i)
        if (values[i] > max_value) {
            max_i = i;
            max_value = values[i];
        }
    return max_i;
}
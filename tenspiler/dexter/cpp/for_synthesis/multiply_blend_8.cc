#include <vector>
#include <cstdint>
using namespace std;

vector<vector<uint8_t>> multiply_blend_8(vector<vector<uint8_t>> base, vector<vector<uint8_t>> active)
{
    vector<vector<uint8_t>> out;
    uint8_t m = base.size();
    uint8_t n = base[0].size();
	for (uint8_t row = 0; row < m; row++) {
        vector<uint8_t> row_vec;
		for (uint8_t col = 0; col < n; col++) {
            uint8_t pixel = (base[row][col] * active[row][col]) / 32;
			row_vec.push_back(pixel);
		}
		out.push_back(row_vec);
	}
	return out;
}
// def multiply_blend_8_ps(base active multiply_blend_8_rv)
// multiply_blend_8_rv == matrix_scalar_div(32, matrix_elemwise_mul(base, active))

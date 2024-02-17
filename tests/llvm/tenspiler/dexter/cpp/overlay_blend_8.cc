#include <vector>
using namespace std;

vector<vector<int>> overlay_blend_8(vector<vector<int>> base, vector<vector<int>> active)
{
    vector<vector<int>> out;
    int m = base.size();
    int n = base[0].size();
	for (int row = 0; row < m; row++) {
        vector<int> row_vec;
		for (int col = 0; col < n; col++) {
			int pixel;
			if (base[row][col] >= 16)
                pixel = 2 * base[row][col] + base[row][col] - 2 * base[row][col] * base[row][col] / 32 - 32;
			else
                pixel = 2 * base[row][col] * base[row][col] / 32;
			row_vec.push_back(pixel);
		}
		out.push_back(row_vec);
	}
	return out;
}
// def overlay_blend_8_ps(base active overlay_blend_8_rv)
// overlay_blend_8_rv == matrix_selection_two_args(base, base, select_two_args)

// def select_two_args(int_x int_y)
// ((((2 * int_x) + int_y) - (((2 * int_y) * int_y) / 32)) - 32) if int_x >= 16 else (((2 * int_y) * int_x) / 32)

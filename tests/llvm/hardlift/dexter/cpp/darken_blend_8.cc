#include <vector>
using namespace std;

vector<vector<int>> darken_blend_8(vector<vector<int>> base, vector<vector<int>> active)
{
    vector<vector<int>> out;
    int m = base.size();
    int n = base[0].size();
	for (int row = 0; row < m; row++) {
        vector<int> row_vec;
		for (int col = 0; col < n; col++) {
			int pixel;
			if (base[row][col] > active[row][col])
				pixel = active[row][col];
			else
				pixel = base[row][col];
			row_vec.push_back(pixel);
		}
		out.push_back(row_vec);
	}
	return out;
}

// def darken_blend_8_ps(base active darken_blend_8_rv)
// darken_blend_8_rv == matrix_selection_two_args(active, base, select_two_args)

// def select_two_args(int_x int_y)
// int_y if int_x > int_y else int_x
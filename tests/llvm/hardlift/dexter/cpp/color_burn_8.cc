#include <vector>
using namespace std;

vector<vector<int>> color_burn_8(vector<vector<int>> base, vector<vector<int>> active)
{
    vector<vector<int>> out;
    int m = base.size();
    int n = base[0].size();
	for (int row = 0; row < m; row++) {
        vector<int> row_vec;
		for (int col = 0; col < n; col++) {
            int pixel;
            if (active[row][col] == 0)
                pixel = 32;
            else
                pixel = 32 - (32 - base[row][col]) / active[row][col];
            row_vec.push_back(pixel);
		}
		out.push_back(row_vec);
	}
	return out;
}
// def color_burn_8_ps(base active color_burn_8_rv)
// color_burn_8_rv == matrix_selection_two_args(active, base, select_two_args)

// def select_two_args(int_x int_y)
// 32 if int_x == 0 else (32 - ((32 - int_y) / int_x))
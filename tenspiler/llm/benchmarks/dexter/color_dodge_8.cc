#include <vector>
using namespace std;

vector<vector<int>> color_dodge_8(vector<vector<int>> base, vector<vector<int>> active)
{
    vector<vector<int>> out;
    int m = base.size();
    int n = base[0].size();
	for (int row = 0; row < m; row++) {
        vector<int> row_vec;
		for (int col = 0; col < n; col++) {
			int pixel;
            if (active[row][col] == 255)
                pixel = 255;
            else
                pixel = base[row][col] / (255 - active[row][col]);
			row_vec.push_back(pixel);
		}
		out.push_back(row_vec);
	}
	return out;
}
// def color_dodge_8_ps(base active color_dodge_8_rv)
// color_dodge_8_rv == matrix_selection_two_args(active, base, select_two_args)

// def select_two_args(int_x int_y)
// 255 if int_x == 255 else (int_y / (255 - int_x))

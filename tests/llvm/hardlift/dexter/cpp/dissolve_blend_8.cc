#include <vector>
using namespace std;

vector<vector<int>> dissolve_blend_8(vector<vector<int>> base, vector<vector<int>> active, int opacity)
{
    vector<vector<int>> out;
    int m = base.size();
    int n = base[0].size();
	for (int row = 0; row < m; row++) {
        vector<int> row_vec;
		for (int col = 0; col < n; col++) {
            int pixel;
            if (opacity - 5 >= 0)
                pixel = active[row][col];
            else
                pixel = base[row][col];
			row_vec.push_back(pixel);
		}
		out.push_back(row_vec);
	}
	return out;
}
// def screen_blend_8_ps(base active screen_blend_8_rv)
// screen_blend_8_rv == matrix_elemwise_sub(matrix_elemwise_add(base, active), matrix_scalar_div(32, matrix_elemwise_mul(base, active)))
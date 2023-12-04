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
			int base_square = base[row][col] * base[row][col];
			int double_base = 2 * base[row][col];
			if (base[row][col] >= 16)
				// pixel = double_base + base[row][col] - 2 * base_square / 32 - 32;
                pixel = 2 * base[row][col] + base[row][col] - 2 * base[row][col] * base[row][col] / 32 - 32;
				// pixel = double_base + base - double_base * base / 32 - 32
			else
				// pixel = 2 * base_square / 32;
                pixel = 2 * base[row][col] * base[row][col] / 32;
				// pixel = double_base * base / 32;
			row_vec.push_back(pixel);
		}
		out.push_back(row_vec);
	}
	return out;
}
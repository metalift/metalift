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

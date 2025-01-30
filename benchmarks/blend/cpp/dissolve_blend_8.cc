#include <vector>
using namespace std;

vector<vector<int>> dissolve_blend_8(vector<vector<int>> base, vector<vector<int>> active, int opacity, int rand_cons)
{
    vector<vector<int>> out;
    int m = base.size();
    int n = base[0].size();
	for (int row = 0; row < m; row++) {
        vector<int> row_vec;
		for (int col = 0; col < n; col++) {
            int rand_val = ((rand_cons % 100) + 1) / 100;
            int pixel;
            if (opacity - rand_val >= 0)
                pixel = active[row][col];
            else
                pixel = base[row][col];
			row_vec.push_back(pixel);
		}
		out.push_back(row_vec);
	}
	return out;
}

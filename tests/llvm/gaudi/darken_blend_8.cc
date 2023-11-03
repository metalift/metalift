#include <vector>
using namespace std;

vector<vector<int>> darken_blend_8(vector<vector<int>> base, vector<vector<int>> active)
{
    vector<vector<int>> out;
    int m = base.size();
    int n = base[0].size();
	for (int row = 0; row < m; row++) {
        vector<int> row_vec;
        out.push_back(row_vec);
		for (int col = 0; col < n; col++) {
			if (base[row][col] > active[row][col])
				row_vec.push_back(active[row][col]);
			else
				row_vec.push_back(base[row][col]);
		}
	}
	return out;
}
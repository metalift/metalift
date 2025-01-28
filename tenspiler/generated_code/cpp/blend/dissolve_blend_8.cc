#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<vector<uint8_t>> dissolve_blend_8(vector<vector<uint8_t>> base, vector<vector<uint8_t>> active, float opacity, int rand_cons)
{
    vector<vector<uint8_t>> out;
    int m = base.size();
    int n = base[0].size();
	for (int row = 0; row < m; row++) {
        vector<uint8_t> row_vec;
		for (int col = 0; col < n; col++) {
            int rand_val = ((rand_cons % 100) + 1) / 100;
            uint8_t pixel;
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

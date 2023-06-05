package original.phoenix;

import java.util.List;

public class LinearRegression {	

	public static class Point {
		public int x, y;
	
		public Point(int x, int y) {
			this.x = x;
			this.y = y;
		}
	}

	public static int[] regress(List<Point> points) {
		int SX_ll = 0, SY_ll = 0, SXX_ll = 0, SYY_ll = 0, SXY_ll = 0;

		// ADD UP RESULTS
		for (int i = 0; i < points.size(); i++) {
			// Compute SX, SY, SYY, SXX, SXY
			SX_ll += points.get(i).x;
			SXX_ll += points.get(i).x * points.get(i).x;
			SY_ll += points.get(i).y;
			SYY_ll += points.get(i).y * points.get(i).y;
			SXY_ll += points.get(i).x * points.get(i).y;
		}
		int[] result = new int[5];
		result[0] = SX_ll;
		result[1] = SXX_ll;
		result[2] = SY_ll;
		result[3] = SYY_ll;
		result[4] = SXY_ll;
		return result;
	}
	
}
package original.phoenix;

import java.util.List;

class Histogram {
	
	public static class Pixel {
		public int r, g, b;
	
		public Pixel(int r, int g, int b) {
			this.r = r;
			this.g = g;
			this.b = b;
		}
	}
	
	public static int[][] histogram(List<Pixel> image, int[] hR, int[] hG, int[] hB) {
		for (int i = 0; i < image.size(); i += 1) {
			int r = image.get(i).r;
			int g = image.get(i).g;
			int b = image.get(i).b;
			hR[r]++;
			hG[g]++;
			hB[b]++;
		}

		int[][] result = new int[3][];
		result[0] = hR;
		result[1] = hG;
		result[2] = hB;

		return result;
	}

}

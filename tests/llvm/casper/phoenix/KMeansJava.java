package original.phoenix;

/**
 * 
 * Translation of Phoenix k-means implementation
 * 
 */

public class KMeansJava {

	private static class Result{
		public Double[][] means;
		public int[] clusters;
		boolean modified;

		Result(Double[][] m, int[] c, boolean mod){
			this.means = m;
			this.clusters = c;
			this.modified = mod;
		}
	}

	final int GRID_SIZE = 1000;

	public static void main(String[] args) {

		int numPoints = 1000, numMeans = 10, dim = 3;

		Double[][] points = generatePoints(numPoints, dim);
		Double[][] means = generatePoints(numMeans, dim);
		int[] clusters = new int[numPoints];

		boolean modified = false;

		while (!modified) {
			modified = findClustersAndCalcMeans(points,means,
					clusters).modified;
		}

		System.out.println("\n\nFinal Means:\n");
		dumpMatrix(means);
	}

	private static void dumpMatrix(Double[][] a) {
		for (int i = 0; i < a.length; i++) {
			for (int j = 0; j < a[i].length; j++)
				System.out.print(" " + a[i][j]);
			System.out.println();
		}
	}

	private static Result findClustersAndCalcMeans(Double[][] points,
			Double[][] means, int[] clusters) {
		int i, j;
		Double minDist, curDist;
		int minIdx;
		int dim = points[0].length;
		boolean modified = false;
		for (i = 0; i < points.length; i++) {
			minDist = getSqDist(points[i], means[0]);
			minIdx = 0;
			for (j = 1; j < means.length; j++) {
				curDist = getSqDist(points[i], means[j]);
				if (curDist < minDist) {
					minDist = curDist;
					minIdx = j;
				}
			}

			if (clusters[i] != minIdx) {
				clusters[i] = minIdx;
				modified = true;
			}
		}

		for (int ii = 0; ii < means.length; ii++) {
			Double[] sum = new Double[dim];
			int groupSize = 0;
			for (int jj = 0; jj < points.length; jj++) {
				if (clusters[jj] == ii) {
					sum = add(sum, points[jj]);
					groupSize++;
				}
			}
			dim = points[0].length;
			Double[] meansi = means[ii];
			for (int kk = 0; kk < dim; kk++) {
				if (groupSize != 0) {
					meansi[kk] = sum[kk] / groupSize;
				}
			}
			means[ii] = meansi;
		}
		return new Result(means, clusters, modified);
	}

	private static Double[] add(Double[] v1, Double[] v2) {
		Double[] sum = new Double[v1.length];
		for (int i = 0; i < sum.length; i++)
			sum[i] = v1[i] + v2[i];
		return sum;
	}

	private static Double getSqDist(Double[] v1, Double[] v2) {
		Double dist = 0.0;
		for (int i = 0; i < v1.length; i++)
			dist += ((v1[i] - v2[i]) * (v1[i] - v2[i]));
		return dist;
	}

	private static Double[][] generatePoints(int numPoints, int dim) {
		Double[][] p = new Double[numPoints][dim];
		for (int i = 0; i < numPoints; i++) {
			p[i] = new Double[dim];
			for (int j = 0; j < dim; j++)
				p[i][j] = Math.random();
		}
		return p;
	}

}
package original.phoenix;

public class PcaJava {

    static final int DEF_GRID_SIZE = 100; // all values in the matrix are from 0
                                          // to this value
    static final int DEF_NUM_ROWS = 3;
    static final int DEF_NUM_COLS = 3;

    static final int num_rows = DEF_NUM_ROWS;
    static final int num_cols = DEF_NUM_COLS;
    static final int grid_size = DEF_GRID_SIZE;

    private static class Result{
        Integer[] mean;
        Integer[][] cov;

        Result(Integer[] m, Integer[][] c){
            this.mean = m;
            this.cov = c;
        }
    }

    /*
     * void parse_args(int argc, String[] argv) { int c; extern char *optarg;
     * extern int optind;
     * 
     * num_rows = DEF_NUM_ROWS; num_cols = DEF_NUM_COLS; grid_size =
     * DEF_GRID_SIZE;
     * 
     * while ((c = getopt(argc, argv, "r:c:s:")) != EOF) { switch (c) { case
     * 'r': num_rows = atoi(optarg); break; case 'c': num_cols = atoi(optarg);
     * break; case 's': grid_size = atoi(optarg); break; case '?':
     * printf("Usage: %s -r <num_rows> -c <num_cols> -s <max value>\n",
     * argv[0]); exit(1); } }
     * 
     * if (num_rows <= 0 || num_cols <= 0 || grid_size <= 0) { printf(
     * "Illegal argument value. All values must be numeric and greater than 0\n"
     * ); exit(1); }
     * 
     * printf("Number of rows = %d\n", num_rows);
     * printf("Number of cols = %d\n", num_cols);
     * printf("Max value for each element = %d\n", grid_size); }
     */

    /**
     * dump_points() Print the values in the matrix to the screen
     */
    static void dump_points(Integer[][] vals, int rows, int cols) {
        int i, j;

        for (i = 0; i < rows; i++) {
            for (j = 0; j < cols; j++) {
                printf("%5d ", vals[i][j]);
            }
            printf("\n");
        }
    }

    /**
     * generate_points() Create the values in the matrix
     */
    static void generate_points(Integer[][] pts, int rows, int cols) {
        int i, j;

        for (i = 0; i < rows; i++) {
            for (j = 0; j < cols; j++) {
                pts[i][j] = rand() % grid_size;
            }
        }
    }

    /**
     * calc_cov() Calculate the covariance
     */
    static Result calc_cov(Integer[][] matrix, Integer[] mean, Integer[][] cov) {
        int i, j, k;
        int sum = 0;

        for (i = 0; i < num_rows; i++) {
            sum = 0;
            for (j = 0; j < num_cols; j++) {
                sum += matrix[i][j];
            }
            mean[i] = sum / num_cols;
        }
        for (i = 0; i < num_rows; i++) {
            for (j = i; j < num_rows; j++) {
                sum = 0;
                for (k = 0; k < num_cols; k++) {
                    sum = sum + ((matrix[i][k] - mean[i]) * (matrix[j][k] - mean[j]));
                }
                int x = sum / (num_cols - 1);
                cov[i][j] = x;
                cov[i][j] = x;
            }
        }
        return new Result(mean, cov);
    }

    public static void main(String[] argv) {

        int i;
        Integer[][] matrix;
        Integer[][] cov;
        Integer[] mean;

        // parse_args(argc, argv);

        // Create the matrix to store the points
        //		matrix = new Integer[num_rows][];
        //		for (i = 0; i < num_rows; i++) {
        //			matrix[i] = new Integer[num_cols];
        //		}

        // Generate random values for all the points in the matrix
        //		generate_points(matrix, num_rows, num_cols);

        // Print the points
        //		dump_points(matrix, num_rows, num_cols);

        matrix = new Integer[][] { new Integer[] { 1, 5, 3 }, new Integer[] { 3, 4, 2 },
                new Integer[] { 11, 2, 4 } };

        // Allocate Memory to store the mean and the covariance matrix
        mean = new Integer[num_rows];
        cov = new Integer[num_rows][];
        for (i = 0; i < num_rows; i++) {
            cov[i] = new Integer[num_rows];
        }

        // Compute the mean and the covariance
        calc_cov(matrix, mean, cov);

        dump_points(cov, num_rows, num_rows);
        return;
    }

    static int rand() {
        int v = (int) (Math.random() * Integer.MAX_VALUE);
        return v;
    }

    static void printf(String fmt, Object... args) {
        System.out.format(fmt, args);
    }

    static void exit(int c) {
        System.exit(c);
    }

}

package original.arithmetic;

import java.util.List;

public class MaxAbs {	
	public static int maxAbsList(List<Integer> data) {
		int max = Integer.MIN_VALUE;
		for(int i=0; i<data.size(); i++) {
			int val = Math.abs(data.get(i));
			if(max < val)
				max = val;
		}
		return max;
	}
}
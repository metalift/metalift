package original.arithmetic;

import java.util.List;

public class Delta {	
	public static int deltaList(List<Integer> data) {
		int min = Integer.MAX_VALUE;
		int max = Integer.MIN_VALUE;
		for(int i=0; i<data.size(); i++) {
			int val = data.get(i);
			if(max < val)
				max = val;
			if(min > val)
				min = val;
		}
		return max-min;
	}
}
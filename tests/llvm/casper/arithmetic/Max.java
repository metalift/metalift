package original.arithmetic;

import java.util.List;

public class Max {	
	public static int maxList(List<Integer> data) {
		int max = Integer.MIN_VALUE;
		for(int i=0; i<data.size(); i++) {
			int val = data.get(i);
			if(max < val)
				max = val;
		}
		return max;
	}
}
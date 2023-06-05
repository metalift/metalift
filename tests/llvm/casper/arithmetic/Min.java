package original.arithmetic;

import java.util.List;

public class Min {
	public static int minList(List<Integer> data) {
		int min = Integer.MAX_VALUE;
		for(int i=0; i<data.size(); i++) {
			int val = data.get(i);
			if(min > val)
				min = val;
		}
		return min;
	}
}
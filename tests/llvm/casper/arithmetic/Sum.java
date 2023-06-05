package original.arithmetic;

import java.util.List;

public class Sum {	
	public static int sumList(List<Integer> data) {
		int sum = 0;
		for(int i=0; i<data.size(); i++) {
			sum += data.get(i);
		}
		return sum;
	}
}
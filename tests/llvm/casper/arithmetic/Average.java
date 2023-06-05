package original.arithmetic;

import java.util.List;

public class Average {	
	public static int avgList(List<Integer> data) {
		int sum = 0;
		int count = 0;
		for(int i=0; i<data.size(); i++) {
			sum += data.get(i);
			count++;
		}
		return sum / count;
	}
}

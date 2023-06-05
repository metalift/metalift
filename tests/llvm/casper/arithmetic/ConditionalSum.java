package original.arithmetic;

import java.util.List;

public class ConditionalSum {	
	public static int sumList(List<Integer> data) {
		int sum = 0;
		for(int i=0; i<data.size(); i++) {
			int var = data.get(i);
			if(var < 100){
				sum += var;
			}
		}
		return sum;
	}
}

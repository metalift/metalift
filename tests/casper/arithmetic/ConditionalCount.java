package original.arithmetic;

import java.util.List;

public class ConditionalCount {	
	public static int countList(List<Integer> data) {
		int count = 0;
		for(int i=0; i<data.size(); i++) {
			int var = data.get(i);
			if(var < 100){
				count++;
			}
		}
		return count;
	}
}

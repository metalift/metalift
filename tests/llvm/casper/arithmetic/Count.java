package original.arithmetic;

import java.util.List;

public class Count {	
	public static int countList(List<Integer> data) {
		int count = 0;
		for(int i=0; i<data.size(); i++) {
			count++;
		}
		return count;
	}
}

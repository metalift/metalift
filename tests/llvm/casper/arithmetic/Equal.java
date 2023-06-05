package original.arithmetic;

import java.util.List;

public class Equal {	
	public static boolean equal(List<Integer> data, int val) {
		boolean equal = true;
		for(int i=0; i<data.size(); i++) {
			if(val != data.get(i)){
				equal = false;
			}
		}
		return equal;
	}
}

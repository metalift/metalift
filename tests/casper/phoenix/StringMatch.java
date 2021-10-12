package original.phoenix;

import java.util.List;

public class StringMatch {
	public static boolean[] matchWords(List<String> words) {
		String key1 = "key1";
		String key2 = "key2";
		String key3 = "key3";
		
		boolean foundKey1 = false;
		boolean foundKey2 = false;
		boolean foundKey3 = false;
		
		for(int i=0; i<words.size(); i++) {
			if(key1.equals(words.get(i)))
				foundKey1 = true;
			if(key2.equals(words.get(i)))
				foundKey2 = true;
			if(key3.equals(words.get(i)))
				foundKey3 = true;
		}
		
		boolean[] res = {foundKey1, foundKey2, foundKey3};
		return res;
	}
}
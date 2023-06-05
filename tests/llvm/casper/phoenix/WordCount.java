package original.phoenix;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class WordCount {
	private static Map<String, Integer> countWords(List<String> words) {
		Map<String, Integer> counts = new HashMap<String, Integer>();
		for (int j = 0; j < words.size(); j++) {
			String word = words.get(j);
			Integer prev = counts.get(word);
			if (prev == null)
				prev = 0;
			counts.put(word, prev + 1);
		}
		return counts;
	}
}

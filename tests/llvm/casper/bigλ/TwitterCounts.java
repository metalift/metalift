package original.bigλ;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class TwitterCounts {
  public Map<String, Integer> pairs(List<String> tweets) {
    Map<String, Integer> result = new HashMap<String, Integer>();

    for (String tweet : tweets) {
      for (String word : tweet.split("\\s+")) {
        if (word.charAt(0) == '#') {
          if (!result.containsKey(word)) {
            result.put(word, 0);
          }
          result.put(word, result.get(word) + 1);
        }
      }
    }

    return result;
  }
}

package original.bigλ;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class ShakespearSentiment {   
  public Map<String,Integer> sentiment(List<String> words) {
    Map<String,Integer> result = new HashMap<String,Integer>();

    result.put("love", 0);
    result.put("hate", 0);

    for (String word : words) {
      if (word.trim().toLowerCase().equals("love")) {
        result.put("love", result.get("love")+1);
      }
      else if (word.trim().toLowerCase().equals("hate")) {
        result.put("hate", result.get("hate")+1);
      }
    }

    return result;
  }
}

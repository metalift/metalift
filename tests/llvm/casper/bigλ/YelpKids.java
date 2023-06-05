package original.bigλ;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class YelpKids {
	class Record {
    public String state;
    public String city;
    public String comment;
    public int score;
    public boolean goodForKids;
	}

	public Map<String,Integer> reviewCount(List<Record> data) {
    Map<String,Integer> result = new HashMap<String,Integer>();
        
    for (Record record : data) {
      if (!result.containsKey(record.city)) {
        result.put(record.city, 0);
      }
      if (record.goodForKids) {
        result.put(record.city, result.get(record.city)+1);
      }
    }

    return result;
  }
}

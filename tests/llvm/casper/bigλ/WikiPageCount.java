package original.bigλ;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class WikiPageCount {
	class Record {
	  public String name;
    public int views;
    public int something;
	}

	public Map<String,Integer> pageCount(List<Record> data) {
    Map<String,Integer> result = new HashMap<String,Integer>();

    for (Record record : data) {
      if (!result.containsKey(record.name)) {
        result.put(record.name, 0);
      }
      result.put(record.name, result.get(record.name) + record.views);
    }
        
    return result;
  }
}
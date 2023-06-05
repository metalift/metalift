package original.bigλ;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class CyclingSpeed {
	class Record {
    public int fst;
    public int snd;
    public int emit;
    public double speed;
	}
       
  public Map<Integer,Integer> cyclingSpeed(List<Record> data) {
    Map<Integer,Integer> result = new HashMap<Integer,Integer>();

    for(Record record : data) {
      int speed = ((int)Math.ceil(record.speed));
      if(!result.containsKey(speed)) {
        result.put(speed,0);
      }
      result.put(speed, result.get(speed)+1);
    }

    return result;
  }
}
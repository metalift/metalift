package original.bigλ;

import java.util.ArrayList;
import java.util.List;

public class DatabaseSelect {

	class Record {
    public List<String> columns;
	}

	public List<Record> select(List<Record> table, String key) {
    List<Record> result = new ArrayList<Record>();

    for (Record record : table) {
      if (record.columns.get(0).equals(key)) {
        result.add(record);
      }
    }

    return result;
  }
}

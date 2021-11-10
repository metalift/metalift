#include "list.h"
#include <iostream>


       
List<int> main(List<int> fst_list, List<int> snd_list, List<int> emit_list, List<int> speed_list) {
    List<int> result;

    for(int i = 0; i < listLength(speed_list) ; i++) {
      int speed = listGet(speed_list, i);
      if(!listGet(result,speed) != NONE) {
        listSet(result,speed,0)];
      }
      listSet (result,speed, listGet(result,speed)+1);
    }

    return result;
}

#include "list.h"
#include <iostream>


       
List<int> main(List<int> fst_list, List<int> snd_list, List<int> emit_list, List<int> speed_list) {
    Array<int> result;

    for(int i = 0; i < listLength(speed_list) ; i++) {
      int speed = arrayGet(speed_list, i);
      if(!arrayGet(result,speed) != NONE) {
        arraySet(result,speed,0)];
      }
      arraySet (result,speed, arrayGet(result,speed)+1);
    }

    return result;
}


// include statements
#include "include/gemmini_params.h"
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void array_sum_gemmini(elem_t arr[LEN][LEN], elem_t n, elem_t* out){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp0[i][0] = arr[i][0]; 
     } 
    tiled_global_average(temp0[0], (elem_t*) out, 1, 1, 1, 1); 
    *out = *out * LEN * LEN; 

}

int32_t array_sum_gemmini_glued (int32_t arr[LEN], int32_t n){
    static elem_t glued_42[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_42[i][0] = arr[i];
    }

    elem_t out;
    array_sum_gemmini(glued_42, n, &out);

    return out;
}


// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void sum_array_gemmini(elem_t a[LEN][LEN], elem_t n, elem_t* out){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp0[i][0] = a[i][0]; 
     } 
    tiled_global_average(temp0[0], (elem_t*) out, 1, 1, 1, 1); 
    *out = *out * LEN * LEN; 

}

int32_t sum_array_gemmini_glued (int32_t a[LEN], int32_t n){
    static elem_t glued_23[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_23[i][0] = a[i];
    }

    elem_t out;
    sum_array_gemmini(glued_23, n, &out);

    return out;
}    

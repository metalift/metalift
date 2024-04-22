
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void linear_burn_8_gemmini(elem_t base[LEN][LEN], elem_t active[LEN][LEN], elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    tiled_resadd_auto(LEN, LEN, 1, 1, 1, base[0], active[0], temp0[0], false, WS); 
    for (int i = 0; i < LEN; i++) { 
     	 for (int j = 0; j < LEN; j++) { 
     	 	 out[i][j] = temp0[i][j] - 255; 
     	 } 
     } 

}

uint8_t* linear_burn_8_gemmini_glued (uint8_t base[LEN][LEN], uint8_t active[LEN][LEN]){
    static uint8_t out [LEN][LEN];
    linear_burn_8_gemmini(base, active, out);

    return out;
}    

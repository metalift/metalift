
// include statements
#include "include/gemmini_params.h"
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void lmsfir1_gemmini(elem_t NTAPS, elem_t input[LEN][LEN], elem_t coefficient[LEN][LEN], elem_t* out){
    static elem_t temp0[LEN][LEN]; 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < NTAPS; i++) { 
     	 temp1[i][0] = input[i][0]; 
     } 
    static elem_t temp2[LEN][LEN]; 
    for (int i = 0; i < NTAPS; i++) { 
     	 temp2[i][0] = coefficient[i][0]; 
     } 
    for (int i = 0; i < NTAPS; i++) { 
     	 temp0[i][0] = temp1[i][0] * temp2[i][0]; 
     } 
    tiled_global_average(temp0[0], (elem_t*) out, 1, 1, 1, 1); 
    *out = *out * LEN * LEN; 

}

int32_t lmsfir1_gemmini_glued (int32_t NTAPS, int32_t input[LEN], int32_t coefficient[LEN]){
    static elem_t glued_46[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_46[i][0] = input[i];
    }

    static elem_t glued_47[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_47[i][0] = coefficient[i];
    }

    elem_t out;
    lmsfir1_gemmini(NTAPS, glued_46, glued_47, &out);

    return out;
}

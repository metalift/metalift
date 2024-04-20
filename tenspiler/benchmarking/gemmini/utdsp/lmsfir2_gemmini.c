
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void lmsfir2_gemmini(elem_t NTAPS, elem_t input[LEN][LEN], elem_t coefficient[LEN][LEN], elem_t error, elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < (NTAPS) - (1); i++) { 
     	 temp0[i][0] = coefficient[i][0]; 
     } 
    static elem_t temp1[LEN][LEN]; 
    static elem_t temp2[LEN][LEN]; 
    for (int i = 0; i < (NTAPS) - (1); i++) { 
     	 temp2[i][0] = input[i][0]; 
     } 
    GEMMINI_ACC_SCALE(temp2, error); 
    memcpy(temp2, temp1, sizeof(elem_t) * LEN * LEN); 
    tiled_resadd_auto((NTAPS) - (1), (NTAPS) - (1), 1, 1, 1, temp0[0], temp1[0], out[0], false, WS); 

}

int32_t* lmsfir2_gemmini_glued (int32_t NTAPS, int32_t input[LEN], int32_t coefficient[LEN], int32_t error){
    static elem_t glued_38[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_38[i][0] = input[i];
    }

    static elem_t glued_39[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_39[i][0] = coefficient[i];
    }

    static int32_t out [LEN][LEN];
    lmsfir2_gemmini(NTAPS, glued_38, glued_39, error, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}    

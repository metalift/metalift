
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void wvec_gemmini(elem_t a[LEN][LEN], elem_t b[LEN][LEN], elem_t m, elem_t n, elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp1[i][0] = a[i][0]; 
     } 
    GEMMINI_ACC_SCALE(temp1, m); 
    memcpy(temp1, temp0, sizeof(elem_t) * LEN * LEN); 
    static elem_t temp2[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp2[i][0] = b[i][0]; 
     } 
    tiled_resadd_auto(n, n, 1, 1, 1, temp0[0], temp2[0], out[0], false, WS); 

}

int32_t* wvec_gemmini_glued (int32_t a[LEN], int32_t b[LEN], int32_t m, int32_t n){
    static elem_t glued_7[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_7[i][0] = a[i];
    }

    static elem_t glued_8[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_8[i][0] = b[i];
    }

    static int32_t out [LEN][LEN];
    wvec_gemmini(glued_7, glued_8, m, n, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}    

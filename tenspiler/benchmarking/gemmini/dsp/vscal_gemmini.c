
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void vscal_gemmini(elem_t arr[LEN][LEN], elem_t v, elem_t n, elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp0[i][0] = arr[i][0]; 
     } 
    GEMMINI_ACC_SCALE(temp0, v); 
    memcpy(temp0, out, sizeof(elem_t) * LEN * LEN); 

}

int32_t* vscal_gemmini_glued (int32_t arr[LEN], int32_t v, int32_t n){
    static elem_t glued_13[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_13[i][0] = arr[i];
    }

    static int32_t out [LEN][LEN];
    vscal_gemmini(glued_13, v, n, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}    

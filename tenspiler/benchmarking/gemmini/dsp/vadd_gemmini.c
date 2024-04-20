
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void vadd_gemmini(elem_t a[LEN][LEN], elem_t b[LEN][LEN], elem_t n, elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp0[i][0] = b[i][0]; 
     } 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp1[i][0] = a[i][0]; 
     } 
    tiled_resadd_auto(n, n, 1, 1, 1, temp0[0], temp1[0], out[0], false, WS); 

}

int32_t* vadd_gemmini_glued (int32_t a[LEN], int32_t b[LEN], int32_t n){
    static elem_t glued_11[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_11[i][0] = a[i];
    }

    static elem_t glued_12[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_12[i][0] = b[i];
    }

    static int32_t out [LEN][LEN];
    vadd_gemmini(glued_11, glued_12, n, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}    

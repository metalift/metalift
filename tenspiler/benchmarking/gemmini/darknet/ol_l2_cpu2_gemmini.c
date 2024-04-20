
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void ol_l2_cpu2_gemmini(elem_t n, elem_t pred[LEN][LEN], elem_t truth[LEN][LEN], elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp0[i][0] = truth[i][0]; 
     } 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp1[i][0] = pred[i][0]; 
     } 
    tiled_resadd_auto(n, n, 1, -1, 1, temp0[0], temp1[0], out[0], false, WS); 

}

int32_t* ol_l2_cpu2_gemmini_glued (int32_t n, int32_t pred[LEN], int32_t truth[LEN]){
    static elem_t glued_32[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_32[i][0] = pred[i];
    }

    static elem_t glued_33[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_33[i][0] = truth[i];
    }

    static int32_t out [LEN][LEN];
    ol_l2_cpu2_gemmini(n, glued_32, glued_33, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}    

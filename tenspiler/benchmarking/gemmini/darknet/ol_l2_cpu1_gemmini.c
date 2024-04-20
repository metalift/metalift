
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void ol_l2_cpu1_gemmini(elem_t n, elem_t pred[LEN][LEN], elem_t truth[LEN][LEN], elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp1[i][0] = pred[i][0]; 
     } 
    static elem_t temp2[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp2[i][0] = truth[i][0]; 
     } 
    tiled_resadd_auto(n, n, 1, -1, 1, temp1[0], temp2[0], temp0[0], false, WS); 
    static elem_t temp3[LEN][LEN]; 
    static elem_t temp4[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp4[i][0] = pred[i][0]; 
     } 
    static elem_t temp5[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp5[i][0] = truth[i][0]; 
     } 
    tiled_resadd_auto(n, n, 1, -1, 1, temp4[0], temp5[0], temp3[0], false, WS); 
    for (int i = 0; i < n; i++) { 
     	 out[i][0] = temp0[i][0] * temp3[i][0]; 
     } 

}

int32_t* ol_l2_cpu1_gemmini_glued (int32_t n, int32_t pred[LEN], int32_t truth[LEN]){
    static elem_t glued_28[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_28[i][0] = pred[i];
    }

    static elem_t glued_29[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_29[i][0] = truth[i];
    }

    static int32_t out [LEN][LEN];
    ol_l2_cpu1_gemmini(n, glued_28, glued_29, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}    

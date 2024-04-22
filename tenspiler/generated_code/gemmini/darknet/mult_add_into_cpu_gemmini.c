
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void mult_add_into_cpu_gemmini(elem_t N, elem_t X[LEN][LEN], elem_t Y[LEN][LEN], elem_t Z[LEN][LEN], elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp0[i][0] = Z[i][0]; 
     } 
    static elem_t temp1[LEN][LEN]; 
    static elem_t temp2[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp2[i][0] = X[i][0]; 
     } 
    static elem_t temp3[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp3[i][0] = Y[i][0]; 
     } 
    for (int i = 0; i < N; i++) { 
     	 temp1[i][0] = temp2[i][0] * temp3[i][0]; 
     } 
    tiled_resadd_auto(N, N, 1, 1, 1, temp0[0], temp1[0], out[0], false, WS); 

}

int32_t* mult_add_into_cpu_gemmini_glued (int32_t N, int32_t X[LEN], int32_t Y[LEN], int32_t Z[LEN]){
    static elem_t glued_26[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_26[i][0] = X[i];
    }

    static elem_t glued_27[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_27[i][0] = Y[i];
    }

    static elem_t glued_28[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_28[i][0] = Z[i];
    }

    static int32_t out [LEN][LEN];
    mult_add_into_cpu_gemmini(N, glued_26, glued_27, glued_28, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}    

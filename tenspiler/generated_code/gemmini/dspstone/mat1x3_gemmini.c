
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void mat1x3_gemmini(elem_t N, elem_t h[LEN][LEN], elem_t x[LEN][LEN], elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 for (int j = 0; j < LEN; j++) { 
     	 	 temp1[i][j] = h[i][j]; 
     	 } 
     } 
    for (int i = 0; i < LEN; i++) { 
     	 for (int j = 0; j < N; j++) { 
     	 	 temp0[i][j] = temp1[i][j]; 
     	 } 
     } 
    static elem_t temp2[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp2[i][0] = x[i][0]; 
     } 
    tiled_matmul_auto(LEN, LEN, 1, (elem_t*) temp0, (elem_t*) temp2, NULL, out, 1, LEN, LEN, LEN, 1, 1, 1, 0, 1, 0, false, false, false, false, 0, 0, WS); 

}

int32_t* mat1x3_gemmini_glued (int32_t N, int32_t h[LEN][LEN], int32_t x[LEN]){
    static elem_t glued_0[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_0[i][0] = x[i];
    }

    static int32_t out [LEN][LEN];
    mat1x3_gemmini(N, h, glued_0, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}    

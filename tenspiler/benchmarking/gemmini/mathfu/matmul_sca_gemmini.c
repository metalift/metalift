
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void matmul_sca_gemmini(elem_t matA[LEN][LEN], elem_t val, elem_t m, elem_t n, elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < m; i++) { 
     	 for (int j = 0; j < LEN; j++) { 
     	 	 temp1[i][j] = matA[i][j]; 
     	 } 
     } 
    for (int i = 0; i < LEN; i++) { 
     	 for (int j = 0; j < n; j++) { 
     	 	 temp0[i][j] = temp1[i][j]; 
     	 } 
     } 
    GEMMINI_ACC_SCALE(temp0, val); 
    memcpy(temp0, out, sizeof(elem_t) * LEN * LEN); 

}

int32_t* matmul_sca_gemmini_glued (int32_t matA[LEN][LEN], int32_t val, int32_t m, int32_t n){
    static int32_t out [LEN][LEN];
    matmul_sca_gemmini(matA, val, m, n, out);

    return out;
}    

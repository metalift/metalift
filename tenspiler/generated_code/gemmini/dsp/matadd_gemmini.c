
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void matadd_gemmini(elem_t matA[LEN][LEN], elem_t matB[LEN][LEN], elem_t m, elem_t n, elem_t out[LEN][LEN]){
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
    static elem_t temp2[LEN][LEN]; 
    static elem_t temp3[LEN][LEN]; 
    for (int i = 0; i < m; i++) { 
     	 for (int j = 0; j < LEN; j++) { 
     	 	 temp3[i][j] = matB[i][j]; 
     	 } 
     } 
    for (int i = 0; i < LEN; i++) { 
     	 for (int j = 0; j < n; j++) { 
     	 	 temp2[i][j] = temp3[i][j]; 
     	 } 
     } 
    tiled_resadd_auto(LEN, LEN, 1, 1, 1, temp0[0], temp2[0], out[0], false, WS); 

}

int32_t* matadd_gemmini_glued (int32_t matA[LEN][LEN], int32_t matB[LEN][LEN], int32_t m, int32_t n){
    static int32_t out [LEN][LEN];
    matadd_gemmini(matA, matB, m, n, out);

    return out;
}    

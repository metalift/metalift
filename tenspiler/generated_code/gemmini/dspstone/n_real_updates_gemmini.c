
// include statements
#include "include/gemmini_params.h"
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void n_real_updates_gemmini(elem_t N, elem_t A[LEN][LEN], elem_t B[LEN][LEN], elem_t C[LEN][LEN], elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp1[i][0] = A[i][0]; 
     } 
    static elem_t temp2[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp2[i][0] = B[i][0]; 
     } 
    for (int i = 0; i < N; i++) { 
     	 temp0[i][0] = temp1[i][0] * temp2[i][0]; 
     } 
    static elem_t temp3[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp3[i][0] = C[i][0]; 
     } 
    tiled_resadd_auto(N, N, 1, 1, 1, temp0[0], temp3[0], out[0], false, WS); 

}

int32_t* n_real_updates_gemmini_glued (int32_t N, int32_t A[LEN], int32_t B[LEN], int32_t C[LEN]){
    static elem_t glued_30[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_30[i][0] = A[i];
    }

    static elem_t glued_31[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_31[i][0] = B[i];
    }

    static elem_t glued_32[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_32[i][0] = C[i];
    }

    static int32_t out [LEN][LEN];
    n_real_updates_gemmini(N, glued_30, glued_31, glued_32, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}

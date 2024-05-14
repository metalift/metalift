
// include statements
#include "include/gemmini_params.h"
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void diveq_sca_gemmini(elem_t a[LEN][LEN], elem_t b, elem_t n, elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp0[i][0] = a[i][0]; 
     } 
    GEMMINI_ACC_SCALE(temp0, 1 / (float)b); 
    memcpy(temp0, out, sizeof(elem_t) * LEN * LEN); 

}

int32_t* diveq_sca_gemmini_glued (int32_t a[LEN], int32_t b, int32_t n){
    static elem_t glued_34[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_34[i][0] = a[i];
    }

    static int32_t out [LEN][LEN];
    diveq_sca_gemmini(glued_34, b, n, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}

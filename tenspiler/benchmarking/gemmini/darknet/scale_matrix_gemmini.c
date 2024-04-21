
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void scale_matrix_gemmini(elem_t m[LEN][LEN], elem_t scale, elem_t out[LEN][LEN]){
    GEMMINI_ACC_SCALE(m, scale); 
    memcpy(m, out, sizeof(elem_t) * LEN * LEN); 

}

int32_t* scale_matrix_gemmini_glued (int32_t m[LEN][LEN], int32_t scale){
    static int32_t out [LEN][LEN];
    scale_matrix_gemmini(m, scale, out);

    return out;
}    

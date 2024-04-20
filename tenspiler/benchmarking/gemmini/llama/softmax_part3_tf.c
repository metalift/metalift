
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void softmax_part3_gemmini(elem_t output[LEN][LEN], elem_t max_pos, elem_t* out){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < max_pos; i++) { 
     	 temp0[i][0] = output[i][0]; 
     } 
    tiled_global_average(temp0[0], (elem_t*) out, 1, 1, 1, 1); 
    *out = *out * LEN * LEN; 

}

float softmax_part3_gemmini_glued (float output[LEN], float max_pos){
    static elem_t glued_44[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_44[i][0] = output[i];
    }

    elem_t out;
    softmax_part3_gemmini(glued_44, max_pos, &out);

    return out;
}    

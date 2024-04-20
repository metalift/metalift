
// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void rmsnorm_part1_gemmini(elem_t input[LEN][LEN], elem_t weight[LEN][LEN], elem_t* out){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < LEN; i++) { 
     	 temp0[i][0] = input[i][0] * input[i][0]; 
     } 
    tiled_global_average(temp0[0], (elem_t*) out, 1, 1, 1, 1); 
    *out = *out * LEN * LEN; 

}

float rmsnorm_part1_gemmini_glued (float input[LEN], float weight[LEN]){
    static elem_t glued_45[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_45[i][0] = input[i];
    }

    static elem_t glued_46[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_46[i][0] = weight[i];
    }

    elem_t out;
    rmsnorm_part1_gemmini(glued_45, glued_46, &out);

    return out;
}    


// include statements
#include "include/gemmini_params.h"
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void matmul_gemmini(elem_t weight[LEN][LEN], elem_t input[LEN][LEN], elem_t out[LEN][LEN]){
    tiled_matmul_auto(LEN, LEN, 1, (elem_t*) weight, (elem_t*) input, NULL, out, 1, LEN, LEN, LEN, 1, 1, 1, 0, 1, 0, false, false, false, false, 0, 0, WS); 

}

float* matmul_gemmini_glued (float weight[LEN][LEN], float input[LEN]){
    static elem_t glued_4[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_4[i][0] = input[i];
    }

    static float out [LEN][LEN];
    matmul_gemmini(weight, glued_4, out);
    static float out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}


// include statements
#include "include/gemmini_params.h"
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void normal_blend_f_gemmini(elem_t base[LEN][LEN], elem_t active[LEN][LEN], elem_t opacity, elem_t out[LEN][LEN]){
    tiled_resadd_auto(LEN, LEN, opacity, (1) - (opacity), 1, active[0], base[0], out[0], false, WS); 

}

uint8_t* normal_blend_f_gemmini_glued (uint8_t base[LEN], uint8_t active[LEN], uint8_t opacity){
    static elem_t glued_2[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_2[i][0] = base[i];
    }

    static elem_t glued_3[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_3[i][0] = active[i];
    }

    static uint8_t out [LEN][LEN];
    normal_blend_f_gemmini(glued_2, glued_3, opacity, out);
    static uint8_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}

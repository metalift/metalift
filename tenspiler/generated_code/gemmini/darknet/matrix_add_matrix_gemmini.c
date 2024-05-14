
// include statements
#include "include/gemmini_params.h"
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void matrix_add_matrix_gemmini(elem_t from_matrix[LEN][LEN], elem_t to_matrix[LEN][LEN], elem_t out[LEN][LEN]){
    tiled_resadd_auto(LEN, LEN, 1, 1, 1, from_matrix[0], to_matrix[0], out[0], false, WS); 

}

int32_t* matrix_add_matrix_gemmini_glued (int32_t from_matrix[LEN][LEN], int32_t to_matrix[LEN][LEN]){
    static int32_t out [LEN][LEN];
    matrix_add_matrix_gemmini(from_matrix, to_matrix, out);

    return out;
}

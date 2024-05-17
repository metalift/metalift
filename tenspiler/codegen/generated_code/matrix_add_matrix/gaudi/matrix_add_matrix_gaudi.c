
void main(tensor from_matrix, tensor to_matrix, tensor matrix_add_matrix_ps_rv) {

    int5 index_space_start = get_index_space_offset();
    int5 index_space_end = index_space_start + get_index_space_size();

    int5 inputCoord = { 0 };
    int5 outputCoord = { 0 };

    unsigned vec_len = 64;

    for(int i = index_space_start[0]; i < index_space_end[0]; i++) {
        #pragma loop_unroll(4)
        for (int j = index_space_start[1]; j < index_space_end[1]; j++) {
            // index space mapping
            // coordinate 0 is for dim0.
            inputCoord[0] = outputCoord[0] = (i * vec_len);
            // coordinate 1 is for dim1.
            inputCoord[1] = outputCoord[1] = j;

            int64 v0 = v_i32_ld_tnsr_b(inputCoord, from_matrix);
            int64 v1 = v_i32_ld_tnsr_b(inputCoord, to_matrix);
            int64 v2 = v_i32_add_b(v0, v1);

            v_i32_st_tnsr(outputCoord, matrix_add_matrix_ps_rv, v2);
        }
    }

}

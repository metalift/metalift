
void main(tensor a, tensor b, int32_t n, tensor muleq_ps_rv) {

    int5 index_space_start = get_index_space_offset();
    int5 index_space_end = index_space_start + get_index_space_size();

    int5 inputCoord = { 0 };
    int5 outputCoord = { 0 };

    unsigned vec_len = 64;

    #pragma loop_unroll(8)
    for(int i = index_space_start[0]; i < index_space_end[0]; i++) {
        // index space mapping
        inputCoord[0] = outputCoord[0] = (i * vec_len);
        int64 v0 = v_i32_ld_tnsr_b(inputCoord, a);
        int64 v1 = v_i32_ld_tnsr_b(inputCoord, b);
        int128 v2 = v_i32_mul_b(v0, v1);
        int64 v3 = v2.v1;
        v_i32_st_tnsr(outputCoord, muleq_ps_rv, v3);
    }

}

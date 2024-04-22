
void main(tensor a, tensor b, int32_t n, tensor diveq_ps_rv) {

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
        float64 v1 = convert_int64_to_float64(v0, 0);
        int64 v2 = v_i32_ld_tnsr_b(inputCoord, b);
        float64 v3 = convert_int64_to_float64(v2, 0);
        float64 v4 = v_reciprocal_fast_f32(v3);
        float64 v5 = v_f32_mul_b(v1, v4);
        int64 v6 = convert_float64_to_int64(v5, 0);
        v_i32_st_tnsr(outputCoord, diveq_ps_rv, v6);
    }

}

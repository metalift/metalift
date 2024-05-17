
void main(tensor base, tensor active, float opacity, tensor normal_blend_f_ps_rv) {

    int5 index_space_start = get_index_space_offset();
    int5 index_space_end = index_space_start + get_index_space_size();

    int5 inputCoord = { 0 };
    int5 outputCoord = { 0 };

    unsigned vec_len = 64;

    #pragma loop_unroll(8)
    for(int i = index_space_start[0]; i < index_space_end[0]; i++) {
        // index space mapping
        inputCoord[0] = outputCoord[0] = (i * vec_len);
        float64 v1 = v_f32_ld_tnsr_b(inputCoord, active);
        float64 v0 = opacity;
        float64 v2 = v_f32_mul_b(v1, v0);
        float64 v7 = v_f32_ld_tnsr_b(inputCoord, base);
        float v3 = 1;
        float v4 = opacity;
        float v5 = v3 - v4;
        float64 v6 = v5;
        float64 v8 = v_f32_mul_b(v7, v6);
        float64 v9 = v_f32_add_b(v2, v8);
        v_f32_st_tnsr(outputCoord, normal_blend_f_ps_rv, v9);
    }

}

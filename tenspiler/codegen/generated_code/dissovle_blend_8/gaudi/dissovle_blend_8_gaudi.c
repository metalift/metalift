
void main(tensor base, tensor active, float opacity, float rand_cons, tensor dissolve_blend_8_ps_rv) {

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

            float v0 = opacity;
            float v1 = rand_cons;
            float v2 = 100;
            float v3 = v1 % v2;
            float v4 = 1;
            float v5 = v3 + v4;
            float v7 = v5 / v2;
            float v8 = v0 - v7;
            float64 v9 = v8;
            float64 v10 = 0;
            float64 v11 = v_f32_ld_tnsr_b(inputCoord, active);
            float64 v12 = v_f32_ld_tnsr_b(inputCoord, base);
            float64 v13 = v_f32_sel_geq_f32_b(v9, v10, v11, v12);

            v_f32_st_tnsr(outputCoord, dissolve_blend_8_ps_rv, v13);
        }
    }

}

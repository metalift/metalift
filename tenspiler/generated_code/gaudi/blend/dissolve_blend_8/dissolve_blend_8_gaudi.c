
void main(tensor base, tensor active, uint8_t opacity, uint8_t rand_cons, tensor dissolve_blend_8_ps_rv) {

    int5 index_space_start = get_index_space_offset();
    int5 index_space_end = index_space_start + get_index_space_size();

    int5 inputCoord = { 0 };
    int5 outputCoord = { 0 };

    unsigned vec_len = 256;

    for(int i = index_space_start[0]; i < index_space_end[0]; i++) {
        #pragma loop_unroll(4)
        for (int j = index_space_start[1]; j < index_space_end[1]; j++) {
            // index space mapping
            // coordinate 0 is for dim0.
            inputCoord[0] = outputCoord[0] = (i * vec_len);
            // coordinate 1 is for dim1.
            inputCoord[1] = outputCoord[1] = j;

            uint8_t v0 = opacity;
            uint8_t v1 = rand_cons;
            uint8_t v2 = 100;
            uint8_t v3 = v1 % v2;
            uint8_t v4 = 1;
            uint8_t v5 = v3 + v4;
            uint8_t v7 = v5 / v2;
            uint8_t v8 = v0 - v7;
            uchar256 v9 = v8;
            uchar256 v10 = 0;
            uchar256 v11 = v_u8_ld_tnsr_b(inputCoord, active);
            uchar256 v12 = v_u8_ld_tnsr_b(inputCoord, base);
            uchar256 v13 = v_u8_sel_geq_u8_b(v9, v10, v11, v12);

            v_u8_st_tnsr(outputCoord, dissolve_blend_8_ps_rv, v13);
        }
    }

}

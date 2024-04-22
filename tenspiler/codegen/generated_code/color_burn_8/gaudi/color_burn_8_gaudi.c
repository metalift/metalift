
void main(tensor base, tensor active, tensor color_burn_8_ps_rv) {

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

            uchar256 v0 = v_u8_ld_tnsr_b(inputCoord, active);
            uchar256 v1 = 0;
            uchar256 v2 = 32;
            uchar256 v5 = v_u8_ld_tnsr_b(inputCoord, base);
            uchar256 v34 = v_u8_sub_b(v2, v5);
            uchar256 v15 = v_u8_ld_tnsr_b(inputCoord, active);
            float256 v16 = convert_uchar256_to_float256(v15, 0);
            float256 v37;
            v37.v1 = v_f32_mul_b(v34.v1, v_reciprocal_fast_f32(v16.v1));
            v37.v2 = v_f32_mul_b(v34.v2, v_reciprocal_fast_f32(v16.v2));
            v37.v3 = v_f32_mul_b(v34.v3, v_reciprocal_fast_f32(v16.v3));
            v37.v4 = v_f32_mul_b(v34.v4, v_reciprocal_fast_f32(v16.v4));
            uchar256 v42 = convert_float256_to_uchar256(v37, SW_RD);
            uchar256 v43 = v_u8_sub_b(v2, v42);
            uchar256 v44 = v_u8_sel_eq_u8_b(v0, v1, v2, v43);

            v_u8_st_tnsr(outputCoord, color_burn_8_ps_rv, v44);
        }
    }

}

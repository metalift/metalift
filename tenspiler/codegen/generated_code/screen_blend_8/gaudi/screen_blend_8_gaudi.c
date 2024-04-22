
void main(tensor base, tensor active, tensor screen_blend_8_ps_rv) {

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

            uchar256 v0 = v_u8_ld_tnsr_b(inputCoord, base);
            uchar256 v1 = v_u8_ld_tnsr_b(inputCoord, active);
            uchar256 v2 = v_u8_add_b(v0, v1);
            uint256 v6 = v_u8_mul_b(v0, v1);
            float256 v7 = convert_uint256_to_float256(v6, SW_LINEAR);
            float64 v3 = 32;
            float64 v8 = v_reciprocal_fast_f32(v3);
            float256 v9;
            v9.v1 = v_f32_mul_b(v7.v1, v8);
            v9.v2 = v_f32_mul_b(v7.v2, v8);
            v9.v3 = v_f32_mul_b(v7.v3, v8);
            v9.v4 = v_f32_mul_b(v7.v4, v8);
            uchar256 v14 = convert_float256_to_uchar256(v9, SW_RD);
            uchar256 v15 = v_u8_sub_b(v2, v14);

            v_u8_st_tnsr(outputCoord, screen_blend_8_ps_rv, v15);
        }
    }

}

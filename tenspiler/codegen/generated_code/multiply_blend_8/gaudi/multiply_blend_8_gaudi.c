
void main(tensor base, tensor active, tensor multiply_blend_8_ps_rv) {

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

            uchar256 v1 = v_u8_ld_tnsr_b(inputCoord, base);
            uchar256 v2 = v_u8_ld_tnsr_b(inputCoord, active);
            uint256 v3 = v_u8_mul_b(v1, v2);
            float256 v4 = convert_uint256_to_float256(v3, SW_LINEAR);
            float64 v0 = 32;
            float64 v5 = v_reciprocal_fast_f32(v0);
            float256 v6;
            v6.v1 = v_f32_mul_b(v4.v1, v5);
            v6.v2 = v_f32_mul_b(v4.v2, v5);
            v6.v3 = v_f32_mul_b(v4.v3, v5);
            v6.v4 = v_f32_mul_b(v4.v4, v5);
            uchar256 v11 = convert_float256_to_uchar256(v6, SW_RD);

            v_u8_st_tnsr(outputCoord, multiply_blend_8_ps_rv, v11);
        }
    }

}

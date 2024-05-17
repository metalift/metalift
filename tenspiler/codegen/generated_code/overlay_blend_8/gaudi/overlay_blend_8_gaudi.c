
void main(tensor base, tensor active, tensor overlay_blend_8_ps_rv) {

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
            uchar256 v1 = 16;
            uchar256 v4 = 2;
            uint256 v184 = v_u8_mul_b(v4, v0);
            uchar256 v185 = convert_uint256_to_uchar256(v184, 0);
            uchar256 v187 = v_u8_add_b(v185, v0);
            uint256 v217 = v_u8_mul_b(v4, v0);
            uchar256 v218 = convert_uint256_to_uchar256(v217, 0);
            uint256 v220 = v_u8_mul_b(v218, v0);
            uchar256 v221 = convert_uint256_to_uchar256(v220, 0);
            float64 v34 = 32;
            float64 v222 = v_reciprocal_fast_f32(v34);
            float256 v223;
            v223.v1 = v_f32_mul_b(v221.v1, v222);
            v223.v2 = v_f32_mul_b(v221.v2, v222);
            v223.v3 = v_f32_mul_b(v221.v3, v222);
            v223.v4 = v_f32_mul_b(v221.v4, v222);
            uchar256 v228 = convert_float256_to_uchar256(v223, SW_RD);
            uchar256 v229 = v_u8_sub_b(v187, v228);
            uchar256 v116 = 32;
            uchar256 v230 = v_u8_sub_b(v229, v116);
            uint256 v260 = v_u8_mul_b(v4, v0);
            uchar256 v261 = convert_uint256_to_uchar256(v260, 0);
            uint256 v263 = v_u8_mul_b(v261, v0);
            uchar256 v264 = convert_uint256_to_uchar256(v263, 0);
            float64 v265 = v_reciprocal_fast_f32(v34);
            float256 v266;
            v266.v1 = v_f32_mul_b(v264.v1, v265);
            v266.v2 = v_f32_mul_b(v264.v2, v265);
            v266.v3 = v_f32_mul_b(v264.v3, v265);
            v266.v4 = v_f32_mul_b(v264.v4, v265);
            uchar256 v271 = convert_float256_to_uchar256(v266, SW_RD);
            uchar256 v272 = v_u8_sel_geq_u8_b(v0, v1, v230, v271);

            v_u8_st_tnsr(outputCoord, overlay_blend_8_ps_rv, v272);
        }
    }

}

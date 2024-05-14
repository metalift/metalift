
void main(tensor base, tensor active, uint8_t opacity, tensor normal_blend_f_ps_rv) {

    int5 index_space_start = get_index_space_offset();
    int5 index_space_end = index_space_start + get_index_space_size();

    int5 inputCoord = { 0 };
    int5 outputCoord = { 0 };

    unsigned vec_len = 256;

    #pragma loop_unroll(8)
    for(int i = index_space_start[0]; i < index_space_end[0]; i++) {
        // index space mapping
        inputCoord[0] = outputCoord[0] = (i * vec_len);
        uchar256 v1 = v_u8_ld_tnsr_b(inputCoord, active);
        uchar256 v0 = opacity;
        uint256 v2 = v_u8_mul_b(v1, v0);
        uchar256 v3 = convert_uint256_to_uchar256(v2, 0);
        uchar256 v8 = v_u8_ld_tnsr_b(inputCoord, base);
        uint8_t v4 = 1;
        uint8_t v5 = opacity;
        uint8_t v6 = v4 - v5;
        uchar256 v7 = v6;
        uint256 v9 = v_u8_mul_b(v8, v7);
        uchar256 v10 = convert_uint256_to_uchar256(v9, 0);
        uchar256 v11 = v_u8_add_b(v3, v10);
        v_u8_st_tnsr(outputCoord, normal_blend_f_ps_rv, v11);
    }

}

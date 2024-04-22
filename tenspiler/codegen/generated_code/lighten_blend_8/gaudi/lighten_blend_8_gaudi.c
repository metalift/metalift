
void main(tensor base, tensor active, tensor lighten_blend_8_ps_rv) {

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
            uchar256 v1 = v_u8_ld_tnsr_b(inputCoord, base);
            uchar256 v4 = v_u8_sel_less_u8_b(v0, v1, v1, v0);

            v_u8_st_tnsr(outputCoord, lighten_blend_8_ps_rv, v4);
        }
    }

}

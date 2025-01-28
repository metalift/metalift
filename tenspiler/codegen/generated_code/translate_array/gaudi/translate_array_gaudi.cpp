
#include <cstring>
// TODO: include your hpp file here

extern unsigned char _binary___translate_array_ps_gaudi2_o_start;
extern unsigned char _binary___translate_array_ps_gaudi2_o_end;


gcapi::GlueCodeReturn_t TranslateArrayPsGaudi2::GetKernelName(
            char kernelName [gcapi::MAX_NODE_NAME])
{
    strcpy(kernelName,"custom_translate_array_ps_gaudi2");
    return gcapi::GLUE_SUCCESS;
}


gcapi::GlueCodeReturn_t TranslateArrayPsGaudi2::GetGcDefinitions(
            gcapi::HabanaKernelParams_t* inDefs,
            gcapi::HabanaKernelInstantiation_t* outDefs) {
    gcapi::GlueCodeReturn_t retVal = setGcDefsHelper(
        inDefs,
        outDefs,
        3,
        1,
        gcapi::DATA_I32
        &_binary___translate_array_ps_gaudi2_o_start,
        &_binary___translate_array_ps_gaudi2_o_end,
    );

    return retVal;
}


#include <cstring>
// TODO: include your hpp file here

extern unsigned char _binary___wvec_ps_gaudi2_o_start;
extern unsigned char _binary___wvec_ps_gaudi2_o_end;


gcapi::GlueCodeReturn_t WvecPsGaudi2::GetKernelName(
            char kernelName [gcapi::MAX_NODE_NAME])
{
    strcpy(kernelName,"custom_wvec_ps_gaudi2");
    return gcapi::GLUE_SUCCESS;
}


gcapi::GlueCodeReturn_t WvecPsGaudi2::GetGcDefinitions(
            gcapi::HabanaKernelParams_t* inDefs,
            gcapi::HabanaKernelInstantiation_t* outDefs) {
    gcapi::GlueCodeReturn_t retVal = setGcDefsHelper(
        inDefs,
        outDefs,
        4,
        1,
        gcapi::DATA_I32
        &_binary___wvec_ps_gaudi2_o_start,
        &_binary___wvec_ps_gaudi2_o_end,
    );

    return retVal;
}


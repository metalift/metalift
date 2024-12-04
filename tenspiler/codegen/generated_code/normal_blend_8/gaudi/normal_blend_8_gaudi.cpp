
#include <cstring>
// TODO: include your hpp file here

extern unsigned char _binary___normal_blend_8_ps_gaudi2_o_start;
extern unsigned char _binary___normal_blend_8_ps_gaudi2_o_end;


gcapi::GlueCodeReturn_t NormalBlend8PsGaudi2::GetKernelName(
            char kernelName [gcapi::MAX_NODE_NAME])
{
    strcpy(kernelName,"custom_normal_blend_8_ps_gaudi2");
    return gcapi::GLUE_SUCCESS;
}


gcapi::GlueCodeReturn_t NormalBlend8PsGaudi2::GetGcDefinitions(
            gcapi::HabanaKernelParams_t* inDefs,
            gcapi::HabanaKernelInstantiation_t* outDefs) {
    gcapi::GlueCodeReturn_t retVal = setGcDefsHelper(
        inDefs,
        outDefs,
        2,
        1,
        gcapi::DATA_U8
        &_binary___normal_blend_8_ps_gaudi2_o_start,
        &_binary___normal_blend_8_ps_gaudi2_o_end,
    );

    // Define scalar params
    NormalBlend8PsParam* paramDef = static_cast<NormalBlend8PsParam*>(in_defs->NodeParams);
    out_defs->kernel.paramsNr = sizeof(*paramDef)/ sizeof(uint8_t);
    memcpy(&(outDefs->kernel.scalarParams[0]), paramDef, sizeof(*paramDef));

    return retVal;
}

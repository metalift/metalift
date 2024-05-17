
#ifndef _NORMAL_BLEND_F_PS_GAUDI2_HPP
#define _NORMAL_BLEND_F_PS_GAUDI2_HPP

#include "gc_interface.h"

class NormalBlendFPsGaudi2
{
    public:
        NormalBlendFPsGaudi2() {}
        virtual ~NormalBlendFPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct NormalBlendFPsParam {
            float opacity;
        };

    private:
        NormalBlendFPsGaudi2(const NormalBlendFPsGaudi2& other) = delete;
        NormalBlendFPsGaudi2& operator=(const NormalBlendFPsGaudi2& other) = delete;
};

#endif

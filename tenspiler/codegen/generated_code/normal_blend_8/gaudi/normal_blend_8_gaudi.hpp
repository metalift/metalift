
#ifndef _NORMAL_BLEND_8_PS_GAUDI2_HPP
#define _NORMAL_BLEND_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class NormalBlend8PsGaudi2
{
    public:
        NormalBlend8PsGaudi2() {}
        virtual ~NormalBlend8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct NormalBlend8PsParam {
            uint8_t opacity;
        };

    private:
        NormalBlend8PsGaudi2(const NormalBlend8PsGaudi2& other) = delete;
        NormalBlend8PsGaudi2& operator=(const NormalBlend8PsGaudi2& other) = delete;
};

#endif

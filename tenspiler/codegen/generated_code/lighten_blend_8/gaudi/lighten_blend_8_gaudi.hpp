
#ifndef _LIGHTEN_BLEND_8_PS_GAUDI2_HPP
#define _LIGHTEN_BLEND_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class LightenBlend8PsGaudi2
{
    public:
        LightenBlend8PsGaudi2() {}
        virtual ~LightenBlend8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        LightenBlend8PsGaudi2(const LightenBlend8PsGaudi2& other) = delete;
        LightenBlend8PsGaudi2& operator=(const LightenBlend8PsGaudi2& other) = delete;
};

#endif

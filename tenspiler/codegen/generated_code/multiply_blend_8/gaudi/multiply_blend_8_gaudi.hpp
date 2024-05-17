
#ifndef _MULTIPLY_BLEND_8_PS_GAUDI2_HPP
#define _MULTIPLY_BLEND_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class MultiplyBlend8PsGaudi2
{
    public:
        MultiplyBlend8PsGaudi2() {}
        virtual ~MultiplyBlend8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        MultiplyBlend8PsGaudi2(const MultiplyBlend8PsGaudi2& other) = delete;
        MultiplyBlend8PsGaudi2& operator=(const MultiplyBlend8PsGaudi2& other) = delete;
};

#endif

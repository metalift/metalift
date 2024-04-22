
#ifndef _DARKEN_BLEND_8_PS_GAUDI2_HPP
#define _DARKEN_BLEND_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class DarkenBlend8PsGaudi2
{
    public:
        DarkenBlend8PsGaudi2() {}
        virtual ~DarkenBlend8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        DarkenBlend8PsGaudi2(const DarkenBlend8PsGaudi2& other) = delete;
        DarkenBlend8PsGaudi2& operator=(const DarkenBlend8PsGaudi2& other) = delete;
};

#endif

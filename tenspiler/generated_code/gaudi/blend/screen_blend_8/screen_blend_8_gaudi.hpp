
#ifndef _SCREEN_BLEND_8_PS_GAUDI2_HPP
#define _SCREEN_BLEND_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class ScreenBlend8PsGaudi2
{
    public:
        ScreenBlend8PsGaudi2() {}
        virtual ~ScreenBlend8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        ScreenBlend8PsGaudi2(const ScreenBlend8PsGaudi2& other) = delete;
        ScreenBlend8PsGaudi2& operator=(const ScreenBlend8PsGaudi2& other) = delete;
};

#endif

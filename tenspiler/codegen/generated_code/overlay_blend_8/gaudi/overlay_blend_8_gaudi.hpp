
#ifndef _OVERLAY_BLEND_8_PS_GAUDI2_HPP
#define _OVERLAY_BLEND_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class OverlayBlend8PsGaudi2
{
    public:
        OverlayBlend8PsGaudi2() {}
        virtual ~OverlayBlend8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        OverlayBlend8PsGaudi2(const OverlayBlend8PsGaudi2& other) = delete;
        OverlayBlend8PsGaudi2& operator=(const OverlayBlend8PsGaudi2& other) = delete;
};

#endif

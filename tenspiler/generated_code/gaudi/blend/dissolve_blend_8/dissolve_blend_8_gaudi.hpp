
#ifndef _DISSOLVE_BLEND_8_PS_GAUDI2_HPP
#define _DISSOLVE_BLEND_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class DissolveBlend8PsGaudi2
{
    public:
        DissolveBlend8PsGaudi2() {}
        virtual ~DissolveBlend8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct DissolveBlend8PsParam {
            uint8_t opacity
            uint8_t rand_cons;
        };

    private:
        DissolveBlend8PsGaudi2(const DissolveBlend8PsGaudi2& other) = delete;
        DissolveBlend8PsGaudi2& operator=(const DissolveBlend8PsGaudi2& other) = delete;
};

#endif

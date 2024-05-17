
#ifndef _COLOR_BURN_8_PS_GAUDI2_HPP
#define _COLOR_BURN_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class ColorBurn8PsGaudi2
{
    public:
        ColorBurn8PsGaudi2() {}
        virtual ~ColorBurn8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        ColorBurn8PsGaudi2(const ColorBurn8PsGaudi2& other) = delete;
        ColorBurn8PsGaudi2& operator=(const ColorBurn8PsGaudi2& other) = delete;
};

#endif

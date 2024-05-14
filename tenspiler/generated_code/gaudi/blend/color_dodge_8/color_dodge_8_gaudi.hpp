
#ifndef _COLOR_DODGE_8_PS_GAUDI2_HPP
#define _COLOR_DODGE_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class ColorDodge8PsGaudi2
{
    public:
        ColorDodge8PsGaudi2() {}
        virtual ~ColorDodge8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        ColorDodge8PsGaudi2(const ColorDodge8PsGaudi2& other) = delete;
        ColorDodge8PsGaudi2& operator=(const ColorDodge8PsGaudi2& other) = delete;
};

#endif

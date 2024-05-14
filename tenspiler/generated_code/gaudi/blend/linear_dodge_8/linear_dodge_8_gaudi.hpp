
#ifndef _LINEAR_DODGE_8_PS_GAUDI2_HPP
#define _LINEAR_DODGE_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class LinearDodge8PsGaudi2
{
    public:
        LinearDodge8PsGaudi2() {}
        virtual ~LinearDodge8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        LinearDodge8PsGaudi2(const LinearDodge8PsGaudi2& other) = delete;
        LinearDodge8PsGaudi2& operator=(const LinearDodge8PsGaudi2& other) = delete;
};

#endif

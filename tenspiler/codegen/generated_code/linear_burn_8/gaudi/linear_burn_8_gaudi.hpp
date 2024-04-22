
#ifndef _LINEAR_BURN_8_PS_GAUDI2_HPP
#define _LINEAR_BURN_8_PS_GAUDI2_HPP

#include "gc_interface.h"

class LinearBurn8PsGaudi2
{
    public:
        LinearBurn8PsGaudi2() {}
        virtual ~LinearBurn8PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        LinearBurn8PsGaudi2(const LinearBurn8PsGaudi2& other) = delete;
        LinearBurn8PsGaudi2& operator=(const LinearBurn8PsGaudi2& other) = delete;
};

#endif

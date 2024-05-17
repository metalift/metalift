
#ifndef _NEGATE_PS_GAUDI2_HPP
#define _NEGATE_PS_GAUDI2_HPP

#include "gc_interface.h"

class NegatePsGaudi2
{
    public:
        NegatePsGaudi2() {}
        virtual ~NegatePsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        NegatePsGaudi2(const NegatePsGaudi2& other) = delete;
        NegatePsGaudi2& operator=(const NegatePsGaudi2& other) = delete;
};

#endif

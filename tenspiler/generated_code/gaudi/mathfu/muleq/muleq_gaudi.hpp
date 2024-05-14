
#ifndef _MULEQ_PS_GAUDI2_HPP
#define _MULEQ_PS_GAUDI2_HPP

#include "gc_interface.h"

class MuleqPsGaudi2
{
    public:
        MuleqPsGaudi2() {}
        virtual ~MuleqPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        MuleqPsGaudi2(const MuleqPsGaudi2& other) = delete;
        MuleqPsGaudi2& operator=(const MuleqPsGaudi2& other) = delete;
};

#endif


#ifndef _MULEQ_SCA_PS_GAUDI2_HPP
#define _MULEQ_SCA_PS_GAUDI2_HPP

#include "gc_interface.h"

class MuleqScaPsGaudi2
{
    public:
        MuleqScaPsGaudi2() {}
        virtual ~MuleqScaPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        MuleqScaPsGaudi2(const MuleqScaPsGaudi2& other) = delete;
        MuleqScaPsGaudi2& operator=(const MuleqScaPsGaudi2& other) = delete;
};

#endif

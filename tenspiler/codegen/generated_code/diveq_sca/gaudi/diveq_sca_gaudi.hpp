
#ifndef _DIVEQ_SCA_PS_GAUDI2_HPP
#define _DIVEQ_SCA_PS_GAUDI2_HPP

#include "gc_interface.h"

class DiveqScaPsGaudi2
{
    public:
        DiveqScaPsGaudi2() {}
        virtual ~DiveqScaPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct DiveqScaPsParam {
            int32_t b
            int32_t n;
        };

    private:
        DiveqScaPsGaudi2(const DiveqScaPsGaudi2& other) = delete;
        DiveqScaPsGaudi2& operator=(const DiveqScaPsGaudi2& other) = delete;
};

#endif

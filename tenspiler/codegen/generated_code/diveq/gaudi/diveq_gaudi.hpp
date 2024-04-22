
#ifndef _DIVEQ_PS_GAUDI2_HPP
#define _DIVEQ_PS_GAUDI2_HPP

#include "gc_interface.h"

class DiveqPsGaudi2
{
    public:
        DiveqPsGaudi2() {}
        virtual ~DiveqPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct DiveqPsParam {
            int32_t n;
        };

    private:
        DiveqPsGaudi2(const DiveqPsGaudi2& other) = delete;
        DiveqPsGaudi2& operator=(const DiveqPsGaudi2& other) = delete;
};

#endif

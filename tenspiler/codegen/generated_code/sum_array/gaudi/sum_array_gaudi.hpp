
#ifndef _SUM_ARRAY_PS_GAUDI2_HPP
#define _SUM_ARRAY_PS_GAUDI2_HPP

#include "gc_interface.h"

class SumArrayPsGaudi2
{
    public:
        SumArrayPsGaudi2() {}
        virtual ~SumArrayPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct SumArrayPsParam {
            int32_t n
            int32_t sum_array_ps_rv;
        };

    private:
        SumArrayPsGaudi2(const SumArrayPsGaudi2& other) = delete;
        SumArrayPsGaudi2& operator=(const SumArrayPsGaudi2& other) = delete;
};

#endif

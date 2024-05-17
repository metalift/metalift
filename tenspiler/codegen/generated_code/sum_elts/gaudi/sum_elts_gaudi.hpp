
#ifndef _SUM_ELTS_PS_GAUDI2_HPP
#define _SUM_ELTS_PS_GAUDI2_HPP

#include "gc_interface.h"

class SumEltsPsGaudi2
{
    public:
        SumEltsPsGaudi2() {}
        virtual ~SumEltsPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        SumEltsPsGaudi2(const SumEltsPsGaudi2& other) = delete;
        SumEltsPsGaudi2& operator=(const SumEltsPsGaudi2& other) = delete;
};

#endif

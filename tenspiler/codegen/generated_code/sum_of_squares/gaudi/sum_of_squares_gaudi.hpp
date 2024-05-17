
#ifndef _SUM_OF_SQUARES_PS_GAUDI2_HPP
#define _SUM_OF_SQUARES_PS_GAUDI2_HPP

#include "gc_interface.h"

class SumOfSquaresPsGaudi2
{
    public:
        SumOfSquaresPsGaudi2() {}
        virtual ~SumOfSquaresPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        SumOfSquaresPsGaudi2(const SumOfSquaresPsGaudi2& other) = delete;
        SumOfSquaresPsGaudi2& operator=(const SumOfSquaresPsGaudi2& other) = delete;
};

#endif

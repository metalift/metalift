
#ifndef _MSE_ARRAY_PS_GAUDI2_HPP
#define _MSE_ARRAY_PS_GAUDI2_HPP

#include "gc_interface.h"

class MseArrayPsGaudi2
{
    public:
        MseArrayPsGaudi2() {}
        virtual ~MseArrayPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct MseArrayPsParam {
            int32_t n
            int32_t mse_array_ps_rv;
        };

    private:
        MseArrayPsGaudi2(const MseArrayPsGaudi2& other) = delete;
        MseArrayPsGaudi2& operator=(const MseArrayPsGaudi2& other) = delete;
};

#endif

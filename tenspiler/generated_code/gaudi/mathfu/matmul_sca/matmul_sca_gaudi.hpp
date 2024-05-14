
#ifndef _MATMUL_SCA_PS_GAUDI2_HPP
#define _MATMUL_SCA_PS_GAUDI2_HPP

#include "gc_interface.h"

class MatmulScaPsGaudi2
{
    public:
        MatmulScaPsGaudi2() {}
        virtual ~MatmulScaPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        MatmulScaPsGaudi2(const MatmulScaPsGaudi2& other) = delete;
        MatmulScaPsGaudi2& operator=(const MatmulScaPsGaudi2& other) = delete;
};

#endif

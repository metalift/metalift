
#ifndef _MULT_ADD_INTO_CPU_PS_GAUDI2_HPP
#define _MULT_ADD_INTO_CPU_PS_GAUDI2_HPP

#include "gc_interface.h"

class MultAddIntoCpuPsGaudi2
{
    public:
        MultAddIntoCpuPsGaudi2() {}
        virtual ~MultAddIntoCpuPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct MultAddIntoCpuPsParam {
            int32_t N;
        };

    private:
        MultAddIntoCpuPsGaudi2(const MultAddIntoCpuPsGaudi2& other) = delete;
        MultAddIntoCpuPsGaudi2& operator=(const MultAddIntoCpuPsGaudi2& other) = delete;
};

#endif

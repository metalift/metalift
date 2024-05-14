
#ifndef _VMUL_PS_GAUDI2_HPP
#define _VMUL_PS_GAUDI2_HPP

#include "gc_interface.h"

class VmulPsGaudi2
{
    public:
        VmulPsGaudi2() {}
        virtual ~VmulPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        VmulPsGaudi2(const VmulPsGaudi2& other) = delete;
        VmulPsGaudi2& operator=(const VmulPsGaudi2& other) = delete;
};

#endif

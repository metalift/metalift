
#ifndef _VADD_PS_GAUDI2_HPP
#define _VADD_PS_GAUDI2_HPP

#include "gc_interface.h"

class VaddPsGaudi2
{
    public:
        VaddPsGaudi2() {}
        virtual ~VaddPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        VaddPsGaudi2(const VaddPsGaudi2& other) = delete;
        VaddPsGaudi2& operator=(const VaddPsGaudi2& other) = delete;
};

#endif

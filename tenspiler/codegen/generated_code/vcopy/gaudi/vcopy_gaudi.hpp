
#ifndef _VCOPY_PS_GAUDI2_HPP
#define _VCOPY_PS_GAUDI2_HPP

#include "gc_interface.h"

class VcopyPsGaudi2
{
    public:
        VcopyPsGaudi2() {}
        virtual ~VcopyPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct VcopyPsParam {
            int32_t n;
        };

    private:
        VcopyPsGaudi2(const VcopyPsGaudi2& other) = delete;
        VcopyPsGaudi2& operator=(const VcopyPsGaudi2& other) = delete;
};

#endif

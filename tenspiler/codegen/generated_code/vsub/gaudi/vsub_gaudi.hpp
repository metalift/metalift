
#ifndef _VSUB_PS_GAUDI2_HPP
#define _VSUB_PS_GAUDI2_HPP

#include "gc_interface.h"

class VsubPsGaudi2
{
    public:
        VsubPsGaudi2() {}
        virtual ~VsubPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct VsubPsParam {
            int32_t n;
        };

    private:
        VsubPsGaudi2(const VsubPsGaudi2& other) = delete;
        VsubPsGaudi2& operator=(const VsubPsGaudi2& other) = delete;
};

#endif

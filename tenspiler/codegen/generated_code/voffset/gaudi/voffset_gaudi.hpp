
#ifndef _VOFFSET_PS_GAUDI2_HPP
#define _VOFFSET_PS_GAUDI2_HPP

#include "gc_interface.h"

class VoffsetPsGaudi2
{
    public:
        VoffsetPsGaudi2() {}
        virtual ~VoffsetPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct VoffsetPsParam {
            int32_t v
            int32_t n;
        };

    private:
        VoffsetPsGaudi2(const VoffsetPsGaudi2& other) = delete;
        VoffsetPsGaudi2& operator=(const VoffsetPsGaudi2& other) = delete;
};

#endif

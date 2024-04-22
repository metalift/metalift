
#ifndef _VSCAL_PS_GAUDI2_HPP
#define _VSCAL_PS_GAUDI2_HPP

#include "gc_interface.h"

class VscalPsGaudi2
{
    public:
        VscalPsGaudi2() {}
        virtual ~VscalPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct VscalPsParam {
            int32_t v
            int32_t n;
        };

    private:
        VscalPsGaudi2(const VscalPsGaudi2& other) = delete;
        VscalPsGaudi2& operator=(const VscalPsGaudi2& other) = delete;
};

#endif

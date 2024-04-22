
#ifndef _LMSFIR1_PS_GAUDI2_HPP
#define _LMSFIR1_PS_GAUDI2_HPP

#include "gc_interface.h"

class Lmsfir1PsGaudi2
{
    public:
        Lmsfir1PsGaudi2() {}
        virtual ~Lmsfir1PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct Lmsfir1PsParam {
            int32_t NTAPS
            int32_t lmsfir1_ps_rv;
        };

    private:
        Lmsfir1PsGaudi2(const Lmsfir1PsGaudi2& other) = delete;
        Lmsfir1PsGaudi2& operator=(const Lmsfir1PsGaudi2& other) = delete;
};

#endif

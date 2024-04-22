
#ifndef _LMSFIR2_PS_GAUDI2_HPP
#define _LMSFIR2_PS_GAUDI2_HPP

#include "gc_interface.h"

class Lmsfir2PsGaudi2
{
    public:
        Lmsfir2PsGaudi2() {}
        virtual ~Lmsfir2PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct Lmsfir2PsParam {
            int32_t NTAPS
            int32_t error;
        };

    private:
        Lmsfir2PsGaudi2(const Lmsfir2PsGaudi2& other) = delete;
        Lmsfir2PsGaudi2& operator=(const Lmsfir2PsGaudi2& other) = delete;
};

#endif

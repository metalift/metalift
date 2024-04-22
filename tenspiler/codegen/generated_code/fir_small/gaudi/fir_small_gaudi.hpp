
#ifndef _FIR_SMALL_PS_GAUDI2_HPP
#define _FIR_SMALL_PS_GAUDI2_HPP

#include "gc_interface.h"

class FirSmallPsGaudi2
{
    public:
        FirSmallPsGaudi2() {}
        virtual ~FirSmallPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct FirSmallPsParam {
            int32_t NTAPS
            int32_t fir_small_ps_rv;
        };

    private:
        FirSmallPsGaudi2(const FirSmallPsGaudi2& other) = delete;
        FirSmallPsGaudi2& operator=(const FirSmallPsGaudi2& other) = delete;
};

#endif


#ifndef _WVEC_PS_GAUDI2_HPP
#define _WVEC_PS_GAUDI2_HPP

#include "gc_interface.h"

class WvecPsGaudi2
{
    public:
        WvecPsGaudi2() {}
        virtual ~WvecPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        WvecPsGaudi2(const WvecPsGaudi2& other) = delete;
        WvecPsGaudi2& operator=(const WvecPsGaudi2& other) = delete;
};

#endif

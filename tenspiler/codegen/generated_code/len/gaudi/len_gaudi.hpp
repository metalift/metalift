
#ifndef _LEN_PS_GAUDI2_HPP
#define _LEN_PS_GAUDI2_HPP

#include "gc_interface.h"

class LenPsGaudi2
{
    public:
        LenPsGaudi2() {}
        virtual ~LenPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        LenPsGaudi2(const LenPsGaudi2& other) = delete;
        LenPsGaudi2& operator=(const LenPsGaudi2& other) = delete;
};

#endif

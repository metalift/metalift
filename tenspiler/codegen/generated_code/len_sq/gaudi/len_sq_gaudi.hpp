
#ifndef _LEN_SQ_PS_GAUDI2_HPP
#define _LEN_SQ_PS_GAUDI2_HPP

#include "gc_interface.h"

class LenSqPsGaudi2
{
    public:
        LenSqPsGaudi2() {}
        virtual ~LenSqPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct LenSqPsParam {
            int32_t n
            int32_t len_sq_ps_rv;
        };

    private:
        LenSqPsGaudi2(const LenSqPsGaudi2& other) = delete;
        LenSqPsGaudi2& operator=(const LenSqPsGaudi2& other) = delete;
};

#endif

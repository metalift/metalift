
#ifndef _MATSCAL_PS_GAUDI2_HPP
#define _MATSCAL_PS_GAUDI2_HPP

#include "gc_interface.h"

class MatscalPsGaudi2
{
    public:
        MatscalPsGaudi2() {}
        virtual ~MatscalPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct MatscalPsParam {
            int32_t val
            int32_t m
            int32_t n;
        };

    private:
        MatscalPsGaudi2(const MatscalPsGaudi2& other) = delete;
        MatscalPsGaudi2& operator=(const MatscalPsGaudi2& other) = delete;
};

#endif

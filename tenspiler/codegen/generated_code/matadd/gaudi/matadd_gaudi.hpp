
#ifndef _MATADD_PS_GAUDI2_HPP
#define _MATADD_PS_GAUDI2_HPP

#include "gc_interface.h"

class MataddPsGaudi2
{
    public:
        MataddPsGaudi2() {}
        virtual ~MataddPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct MataddPsParam {
            int32_t m
            int32_t n;
        };

    private:
        MataddPsGaudi2(const MataddPsGaudi2& other) = delete;
        MataddPsGaudi2& operator=(const MataddPsGaudi2& other) = delete;
};

#endif

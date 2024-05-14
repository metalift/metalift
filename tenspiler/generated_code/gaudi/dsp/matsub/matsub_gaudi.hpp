
#ifndef _MATSUB_PS_GAUDI2_HPP
#define _MATSUB_PS_GAUDI2_HPP

#include "gc_interface.h"

class MatsubPsGaudi2
{
    public:
        MatsubPsGaudi2() {}
        virtual ~MatsubPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        MatsubPsGaudi2(const MatsubPsGaudi2& other) = delete;
        MatsubPsGaudi2& operator=(const MatsubPsGaudi2& other) = delete;
};

#endif

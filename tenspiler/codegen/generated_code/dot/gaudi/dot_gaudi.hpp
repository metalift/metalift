
#ifndef _DOT_PS_GAUDI2_HPP
#define _DOT_PS_GAUDI2_HPP

#include "gc_interface.h"

class DotPsGaudi2
{
    public:
        DotPsGaudi2() {}
        virtual ~DotPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        DotPsGaudi2(const DotPsGaudi2& other) = delete;
        DotPsGaudi2& operator=(const DotPsGaudi2& other) = delete;
};

#endif

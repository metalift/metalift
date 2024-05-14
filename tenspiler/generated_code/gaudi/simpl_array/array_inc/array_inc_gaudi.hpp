
#ifndef _ARRAY_INC_PS_GAUDI2_HPP
#define _ARRAY_INC_PS_GAUDI2_HPP

#include "gc_interface.h"

class ArrayIncPsGaudi2
{
    public:
        ArrayIncPsGaudi2() {}
        virtual ~ArrayIncPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        ArrayIncPsGaudi2(const ArrayIncPsGaudi2& other) = delete;
        ArrayIncPsGaudi2& operator=(const ArrayIncPsGaudi2& other) = delete;
};

#endif

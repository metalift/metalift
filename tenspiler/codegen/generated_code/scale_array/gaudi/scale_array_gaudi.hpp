
#ifndef _SCALE_ARRAY_PS_GAUDI2_HPP
#define _SCALE_ARRAY_PS_GAUDI2_HPP

#include "gc_interface.h"

class ScaleArrayPsGaudi2
{
    public:
        ScaleArrayPsGaudi2() {}
        virtual ~ScaleArrayPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct ScaleArrayPsParam {
            int32_t n
            int32_t s;
        };

    private:
        ScaleArrayPsGaudi2(const ScaleArrayPsGaudi2& other) = delete;
        ScaleArrayPsGaudi2& operator=(const ScaleArrayPsGaudi2& other) = delete;
};

#endif

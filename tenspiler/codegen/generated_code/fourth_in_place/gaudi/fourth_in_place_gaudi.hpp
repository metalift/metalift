
#ifndef _FOURTH_IN_PLACE_PS_GAUDI2_HPP
#define _FOURTH_IN_PLACE_PS_GAUDI2_HPP

#include "gc_interface.h"

class FourthInPlacePsGaudi2
{
    public:
        FourthInPlacePsGaudi2() {}
        virtual ~FourthInPlacePsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct FourthInPlacePsParam {
            int32_t n;
        };

    private:
        FourthInPlacePsGaudi2(const FourthInPlacePsGaudi2& other) = delete;
        FourthInPlacePsGaudi2& operator=(const FourthInPlacePsGaudi2& other) = delete;
};

#endif

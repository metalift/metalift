
#ifndef _CUBE_IN_PLACE_PS_GAUDI2_HPP
#define _CUBE_IN_PLACE_PS_GAUDI2_HPP

#include "gc_interface.h"

class CubeInPlacePsGaudi2
{
    public:
        CubeInPlacePsGaudi2() {}
        virtual ~CubeInPlacePsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct CubeInPlacePsParam {
            int32_t n;
        };

    private:
        CubeInPlacePsGaudi2(const CubeInPlacePsGaudi2& other) = delete;
        CubeInPlacePsGaudi2& operator=(const CubeInPlacePsGaudi2& other) = delete;
};

#endif

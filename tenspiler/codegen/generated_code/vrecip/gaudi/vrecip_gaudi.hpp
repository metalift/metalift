
#ifndef _VRECIP_PS_GAUDI2_HPP
#define _VRECIP_PS_GAUDI2_HPP

#include "gc_interface.h"

class VrecipPsGaudi2
{
    public:
        VrecipPsGaudi2() {}
        virtual ~VrecipPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct VrecipPsParam {
            int32_t n;
        };

    private:
        VrecipPsGaudi2(const VrecipPsGaudi2& other) = delete;
        VrecipPsGaudi2& operator=(const VrecipPsGaudi2& other) = delete;
};

#endif

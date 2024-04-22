
#ifndef _VNEG_PS_GAUDI2_HPP
#define _VNEG_PS_GAUDI2_HPP

#include "gc_interface.h"

class VnegPsGaudi2
{
    public:
        VnegPsGaudi2() {}
        virtual ~VnegPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct VnegPsParam {
            int32_t n;
        };

    private:
        VnegPsGaudi2(const VnegPsGaudi2& other) = delete;
        VnegPsGaudi2& operator=(const VnegPsGaudi2& other) = delete;
};

#endif


#ifndef _MAG_ARRAY_PS_GAUDI2_HPP
#define _MAG_ARRAY_PS_GAUDI2_HPP

#include "gc_interface.h"

class MagArrayPsGaudi2
{
    public:
        MagArrayPsGaudi2() {}
        virtual ~MagArrayPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct MagArrayPsParam {
            int32_t n
            int32_t mag_array_ps_rv;
        };

    private:
        MagArrayPsGaudi2(const MagArrayPsGaudi2& other) = delete;
        MagArrayPsGaudi2& operator=(const MagArrayPsGaudi2& other) = delete;
};

#endif

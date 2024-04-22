
#ifndef _SUBEQ_SCA_PS_GAUDI2_HPP
#define _SUBEQ_SCA_PS_GAUDI2_HPP

#include "gc_interface.h"

class SubeqScaPsGaudi2
{
    public:
        SubeqScaPsGaudi2() {}
        virtual ~SubeqScaPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct SubeqScaPsParam {
            int32_t b
            int32_t n;
        };

    private:
        SubeqScaPsGaudi2(const SubeqScaPsGaudi2& other) = delete;
        SubeqScaPsGaudi2& operator=(const SubeqScaPsGaudi2& other) = delete;
};

#endif

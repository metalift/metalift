
#ifndef _SUBEQ_PS_GAUDI2_HPP
#define _SUBEQ_PS_GAUDI2_HPP

#include "gc_interface.h"

class SubeqPsGaudi2
{
    public:
        SubeqPsGaudi2() {}
        virtual ~SubeqPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct SubeqPsParam {
            int32_t n;
        };

    private:
        SubeqPsGaudi2(const SubeqPsGaudi2& other) = delete;
        SubeqPsGaudi2& operator=(const SubeqPsGaudi2& other) = delete;
};

#endif

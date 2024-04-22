
#ifndef _OL_L2_CPU2_PS_GAUDI2_HPP
#define _OL_L2_CPU2_PS_GAUDI2_HPP

#include "gc_interface.h"

class OlL2Cpu2PsGaudi2
{
    public:
        OlL2Cpu2PsGaudi2() {}
        virtual ~OlL2Cpu2PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct OlL2Cpu2PsParam {
            int32_t n;
        };

    private:
        OlL2Cpu2PsGaudi2(const OlL2Cpu2PsGaudi2& other) = delete;
        OlL2Cpu2PsGaudi2& operator=(const OlL2Cpu2PsGaudi2& other) = delete;
};

#endif

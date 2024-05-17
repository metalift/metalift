
#ifndef _OL_L2_CPU1_PS_GAUDI2_HPP
#define _OL_L2_CPU1_PS_GAUDI2_HPP

#include "gc_interface.h"

class OlL2Cpu1PsGaudi2
{
    public:
        OlL2Cpu1PsGaudi2() {}
        virtual ~OlL2Cpu1PsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        OlL2Cpu1PsGaudi2(const OlL2Cpu1PsGaudi2& other) = delete;
        OlL2Cpu1PsGaudi2& operator=(const OlL2Cpu1PsGaudi2& other) = delete;
};

#endif

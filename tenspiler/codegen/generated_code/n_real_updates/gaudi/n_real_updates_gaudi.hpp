
#ifndef _N_REAL_UPDATES_PS_GAUDI2_HPP
#define _N_REAL_UPDATES_PS_GAUDI2_HPP

#include "gc_interface.h"

class NRealUpdatesPsGaudi2
{
    public:
        NRealUpdatesPsGaudi2() {}
        virtual ~NRealUpdatesPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        NRealUpdatesPsGaudi2(const NRealUpdatesPsGaudi2& other) = delete;
        NRealUpdatesPsGaudi2& operator=(const NRealUpdatesPsGaudi2& other) = delete;
};

#endif

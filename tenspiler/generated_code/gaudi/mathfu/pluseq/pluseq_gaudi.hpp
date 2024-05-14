
#ifndef _PLUSEQ_PS_GAUDI2_HPP
#define _PLUSEQ_PS_GAUDI2_HPP

#include "gc_interface.h"

class PluseqPsGaudi2
{
    public:
        PluseqPsGaudi2() {}
        virtual ~PluseqPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        PluseqPsGaudi2(const PluseqPsGaudi2& other) = delete;
        PluseqPsGaudi2& operator=(const PluseqPsGaudi2& other) = delete;
};

#endif

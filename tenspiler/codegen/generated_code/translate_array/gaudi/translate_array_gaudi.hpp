
#ifndef _TRANSLATE_ARRAY_PS_GAUDI2_HPP
#define _TRANSLATE_ARRAY_PS_GAUDI2_HPP

#include "gc_interface.h"

class TranslateArrayPsGaudi2
{
    public:
        TranslateArrayPsGaudi2() {}
        virtual ~TranslateArrayPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct TranslateArrayPsParam {
            int32_t n
            int32_t s;
        };

    private:
        TranslateArrayPsGaudi2(const TranslateArrayPsGaudi2& other) = delete;
        TranslateArrayPsGaudi2& operator=(const TranslateArrayPsGaudi2& other) = delete;
};

#endif


#ifndef _SCALE_MATRIX_PS_GAUDI2_HPP
#define _SCALE_MATRIX_PS_GAUDI2_HPP

#include "gc_interface.h"

class ScaleMatrixPsGaudi2
{
    public:
        ScaleMatrixPsGaudi2() {}
        virtual ~ScaleMatrixPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


        struct ScaleMatrixPsParam {
            int32_t scale;
        };

    private:
        ScaleMatrixPsGaudi2(const ScaleMatrixPsGaudi2& other) = delete;
        ScaleMatrixPsGaudi2& operator=(const ScaleMatrixPsGaudi2& other) = delete;
};

#endif

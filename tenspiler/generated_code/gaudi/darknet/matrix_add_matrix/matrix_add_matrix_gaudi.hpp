
#ifndef _MATRIX_ADD_MATRIX_PS_GAUDI2_HPP
#define _MATRIX_ADD_MATRIX_PS_GAUDI2_HPP

#include "gc_interface.h"

class MatrixAddMatrixPsGaudi2
{
    public:
        MatrixAddMatrixPsGaudi2() {}
        virtual ~MatrixAddMatrixPsGaudi2() {}

        virtual gcapi::GlueCodeReturn_t
        GetGcDefinitions(gcapi::HabanaKernelParams_t* inDefs,
                    gcapi::HabanaKernelInstantiation_t* outDefs);

        virtual gcapi::GlueCodeReturn_t GetKernelName(
                char kernelName [gcapi::MAX_NODE_NAME]);


    private:
        MatrixAddMatrixPsGaudi2(const MatrixAddMatrixPsGaudi2& other) = delete;
        MatrixAddMatrixPsGaudi2& operator=(const MatrixAddMatrixPsGaudi2& other) = delete;
};

#endif

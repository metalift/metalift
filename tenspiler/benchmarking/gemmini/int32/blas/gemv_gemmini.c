
// setup code
#include <stdint.h>
#include <stddef.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#ifndef BAREMETAL
#include <sys/mman.h>
#endif
#include "include/gemmini_testutils.h"

# define LEN 500

uint64_t start = 0;
uint64_t end = 0;

float random_float() {
    return (float)(rand()) / (float)(RAND_MAX);
}

uint8_t random_uint8() {
    return (uint8_t)(rand() % 256 - 128);  
}

int32_t random_int() {
    return rand();  
}


// include statements 
#include "include/gemmini_params.h" 
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void gemv_gemmini(elem_t M, elem_t N, elem_t A[LEN][LEN], elem_t x[LEN][LEN], elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < M; i++) { 
     	 for (int j = 0; j < LEN; j++) { 
     	 	 temp1[i][j] = A[i][j]; 
     	 } 
     } 
    for (int i = 0; i < LEN; i++) { 
     	 for (int j = 0; j < N; j++) { 
     	 	 temp0[i][j] = temp1[i][j]; 
     	 } 
     } 
    static elem_t temp2[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp2[i][0] = x[i][0]; 
     } 
    tiled_matmul_auto(LEN, LEN, 1, (elem_t*) temp0, (elem_t*) temp2, NULL, out, 1, LEN, LEN, LEN, 1, 1, 1, 0, 1, 0, false, false, false, false, 0, 0, WS); 

}

int32_t* gemv_gemmini_glued (int32_t M, int32_t N, int32_t A[LEN][LEN], int32_t x[LEN]){
    static elem_t glued_22[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_22[i][0] = x[i];
    }

    static int32_t out [LEN][LEN];
    gemv_gemmini(M, N, A, glued_22, out);
    static int32_t out_postprocess [LEN]; 


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}    

int main() {
#ifndef BAREMETAL
    if (mlockall(MCL_CURRENT | MCL_FUTURE) != 0) {
      perror("mlockall failed");
      exit(1);
    }
#endif

    gemmini_flush(0);
    unsigned long long totalTime = 0;

    static int32_t w[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        for (int j = 0; j < LEN; j++) {
            w[i][j] = random_int();
        }
    }

    int32_t m = LEN;
    int32_t n = LEN;

    static int32_t w2[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        w2[i][0] = random_int();
    }
    static int32_t out [LEN][LEN];
    start = read_cycles();
    gemv_gemmini(m, n, w, w2, out);
    end = read_cycles();
    totalTime += end - start;

  
  
    printf("gemv_gemmini_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}
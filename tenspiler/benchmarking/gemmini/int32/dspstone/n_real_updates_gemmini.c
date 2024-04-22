
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

# define LEN 488

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

void n_real_updates_gemmini(elem_t N, elem_t A[LEN][LEN], elem_t B[LEN][LEN], elem_t C[LEN][LEN], elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp1[i][0] = B[i][0]; 
     } 
    static elem_t temp2[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp2[i][0] = A[i][0]; 
     } 
    for (int i = 0; i < N; i++) { 
     	 temp0[i][0] = temp1[i][0] * temp2[i][0]; 
     } 
    static elem_t temp3[LEN][LEN]; 
    for (int i = 0; i < N; i++) { 
     	 temp3[i][0] = C[i][0]; 
     } 
    tiled_resadd_auto(N, N, 1, 1, 1, temp0[0], temp3[0], out[0], false, WS); 

}

int32_t* n_real_updates_gemmini_glued (int32_t N, int32_t A[LEN], int32_t B[LEN], int32_t C[LEN]){
    static elem_t glued_1[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_1[i][0] = A[i];
    }

    static elem_t glued_2[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_2[i][0] = B[i];
    }

    static elem_t glued_3[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_3[i][0] = C[i];
    }

    static int32_t out [LEN][LEN];
    n_real_updates_gemmini(N, glued_1, glued_2, glued_3, out);
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
        w[i][0] = random_int();
    }
    static int32_t w2[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        w2[i][0] = random_int();
    }
        static int32_t w3[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        w3[i][0] = random_int();
    }
    int32_t N = LEN;
    static int32_t out [LEN][LEN];
    start = read_cycles();
    n_real_updates_gemmini(N, w, w2, w3, out);
    end = read_cycles();

    totalTime += end - start;

  
  
    printf("n_real_updates_gemmini_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}

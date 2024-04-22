
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

void vscal_gemmini(elem_t arr[LEN][LEN], elem_t v, elem_t n, elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp0[i][0] = arr[i][0]; 
     } 
    GEMMINI_ACC_SCALE(temp0, v); 
    memcpy(temp0, out, sizeof(elem_t) * LEN * LEN); 

}

int32_t* vscal_gemmini_glued (int32_t arr[LEN], int32_t v, int32_t n){
    static elem_t glued_13[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_13[i][0] = arr[i];
    }

    static int32_t out [LEN][LEN];
    vscal_gemmini(glued_13, v, n, out);
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


    
    int32_t n = LEN;
    int32_t s = random_int();
    static int32_t out [LEN][LEN];
    start = read_cycles();
    vscal_gemmini(w, s, n, out);
    end = read_cycles();

    totalTime += end - start;
  
    printf("vscal_gemmini_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}

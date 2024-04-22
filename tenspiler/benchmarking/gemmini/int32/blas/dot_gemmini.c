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

# define LEN 122

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

void dot_gemmini(elem_t a[LEN][LEN], elem_t b[LEN][LEN], elem_t n, elem_t* out){
    static elem_t temp0[LEN][LEN]; 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp1[i][0] = b[i][0]; 
     } 
    static elem_t temp2[LEN][LEN]; 
    for (int i = 0; i < n; i++) { 
     	 temp2[i][0] = a[i][0]; 
     } 
    for (int i = 0; i < n; i++) { 
     	 temp0[i][0] = temp1[i][0] * temp2[i][0]; 
     } 
    tiled_global_average(temp0[0], (elem_t*) out, 1, 1, 1, 1); 
    *out = *out * LEN * LEN; 

}

int32_t dot_gemmini_glued (int32_t a[LEN], int32_t b[LEN], int32_t n){
    static elem_t glued_23[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_23[i][0] = a[i];
    }

    static elem_t glued_24[LEN][LEN];

    for (int i = 0; i < LEN; i++) { 
        glued_24[i][0] = b[i];
    }

    elem_t out;
    dot_gemmini(glued_23, glued_24, n, &out);

    return out;
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
    int32_t n = LEN;
    elem_t out;
    start = read_cycles();
    dot_gemmini(w, w2, n, &out);
    end = read_cycles();
    totalTime += end - start;

  
  
    printf("dot_gemmini_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}
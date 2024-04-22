
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

void matsub_gemmini(elem_t matA[LEN][LEN], elem_t matB[LEN][LEN], elem_t m, elem_t n, elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN]; 
    static elem_t temp1[LEN][LEN]; 
    for (int i = 0; i < m; i++) { 
     	 for (int j = 0; j < LEN; j++) { 
     	 	 temp1[i][j] = matA[i][j]; 
     	 } 
     } 
    for (int i = 0; i < LEN; i++) { 
     	 for (int j = 0; j < n; j++) { 
     	 	 temp0[i][j] = temp1[i][j]; 
     	 } 
     } 
    static elem_t temp2[LEN][LEN]; 
    static elem_t temp3[LEN][LEN]; 
    for (int i = 0; i < m; i++) { 
     	 for (int j = 0; j < LEN; j++) { 
     	 	 temp3[i][j] = matB[i][j]; 
     	 } 
     } 
    for (int i = 0; i < LEN; i++) { 
     	 for (int j = 0; j < n; j++) { 
     	 	 temp2[i][j] = temp3[i][j]; 
     	 } 
     } 
    tiled_resadd_auto(LEN, LEN, 1, -1, 1, temp0[0], temp2[0], out[0], false, WS); 

}

int32_t* matsub_gemmini_glued (int32_t matA[LEN][LEN], int32_t matB[LEN][LEN], int32_t m, int32_t n){
    static int32_t out [LEN][LEN];
    matsub_gemmini(matA, matB, m, n, out);

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
        for (int j = 0; j < LEN; j++) {
            w[i][j] = random_int();
        }
    }    
    static int32_t w2[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        for (int j = 0; j < LEN; j++) {
            w2[i][j] = random_int();
        }
    }
    int32_t m = LEN;
    int32_t n = LEN;
    static int32_t out [LEN][LEN];
    start = read_cycles();
    matsub_gemmini(w, w2, m, n, out);
    end = read_cycles();

    totalTime += end - start;

    printf("matsub_gemmini_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}

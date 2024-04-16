
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

# define IMAGE_LEN 500
# define LEN 250000

unsigned long long start = 0;
unsigned long long end = 0;

float random_float() {
    return (float)(rand()) / (float)(RAND_MAX);
}


// include statements
#include "include/gemmini_params.h"
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void normal_blend_f_gemmini(elem_t base[LEN][LEN], elem_t active[LEN][LEN], elem_t opacity, elem_t out[LEN][LEN]){
    tiled_resadd_auto(LEN, LEN, opacity, (1) - (opacity), 1, active[0], base[0], out[0], false, WS);

}

float* normal_blend_f_gemmini_glued (float base[LEN], float active[LEN], float opacity){
    static elem_t glued_0[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_0[i][0] = base[i];
    }

    static elem_t glued_1[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_1[i][0] = active[i];
    }

    static float out [LEN][LEN];
    start = read_cycles();
    normal_blend_f_gemmini(glued_0, glued_1, opacity, out);
    end = read_cycles();
    static float out_postprocess [LEN];


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
  srand(1);
  gemmini_flush(0);
  unsigned long long totalTime = 0;
  static float base[LEN];
  static float active[LEN];
  for (int i = 0; i < LEN; i++) {
    base[i] = random_float();
    active[i] = random_float();
  }
  float opacity = random_float();
  normal_blend_f_gemmini_glued(base, active, opacity);

  totalTime += end - start;



  printf("normal_blend_f");
  printf("%llu\n", totalTime);
  exit(0);
}

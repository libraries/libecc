#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

#include "../external_deps/print.h"
#include "../external_deps/rand.h"
#include "../libec.h"

int LLVMFuzzerTestOneInput(uint8_t *data, size_t size) {
  u8 buf[128];
  for (int i = 0; i < 128 && i < size; i++) {
    buf[i] = data[i];
  }
  size_t bpt = 0;

  nn a, b, c, d;
  nn_init_from_buf(&a, &buf[bpt], 32);
  bpt += 32;
  nn_init_from_buf(&b, &buf[bpt], 32);
  bpt += 32;
  nn_init_from_buf(&c, &buf[bpt], 32);
  bpt += 32;
  nn_init_from_buf(&d, &buf[bpt], 32);
  bpt += 32;
  if (nn_iszero(&a)) {
    nn_one(&a);
  }
  if (nn_iszero(&b)) {
    nn_one(&b);
  }
  if (nn_iszero(&c)) {
    nn_one(&c);
  }
  if (nn_iszero(&d)) {
    nn_one(&d);
  }

  ec_params params;
  import_params(&params, &secp256r1_str_params);

  prj_pt e, f;
  prj_pt_mul_monty(&e, &c, &params.ec_gen);
  prj_pt_mul_monty(&f, &d, &params.ec_gen);
  prj_pt_normalize(&e);
  prj_pt_normalize(&f);

  prj_pt g, h, i, j;
  prj_pt_mul_monty(&g, &a, &e);
  prj_pt_mul_monty(&h, &b, &f);
  prj_pt_add_monty(&i, &g, &h);
  prj_pt_ec_mult_wnaf(&j, &a, &e, &b, &f);

  assert(prj_pt_is_on_curve(&i));
  assert(prj_pt_is_on_curve(&j));
  assert(prj_pt_cmp(&i, &j) == 0);

  return 0;
}

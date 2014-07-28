#include "print-impl.h"

#include "blake2/blake2.h"

#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define GKNLEN   64
#define KEYLEN   40
#define BKNLEN   40
#define TAGLEN   64
#define BLOCKLEN 65536

typedef uint32_t v8u __attribute__((ext_vector_type(8)));

static const uint8_t salsa_sigma[16] = "expand 32-byte k";

#define rotate(X, S) \
  (((X) << S) ^ ((X) >> (32 - S)))

#define memcompare memcmp

// The HSalsa core
static inline void hsalsa_core(v8u* x) {
   x[4] ^= rotate( x[0]+x[12],  7);
   x[8] ^= rotate( x[4]+ x[0],  9);
  x[12] ^= rotate( x[8]+ x[4], 13);
   x[0] ^= rotate(x[12]+ x[8], 18);

   x[9] ^= rotate( x[5]+ x[1],  7);
  x[13] ^= rotate( x[9]+ x[5],  9);
   x[1] ^= rotate(x[13]+ x[9], 13);
   x[5] ^= rotate( x[1]+x[13], 18);

  x[14] ^= rotate(x[10]+ x[6],  7);
   x[2] ^= rotate(x[14]+x[10],  9);
   x[6] ^= rotate( x[2]+x[14], 13);
  x[10] ^= rotate( x[6]+ x[2], 18);

   x[3] ^= rotate(x[15]+x[11],  7);
   x[7] ^= rotate( x[3]+x[15],  9);
  x[11] ^= rotate( x[7]+ x[3], 13);
  x[15] ^= rotate(x[11]+ x[7], 18);

   x[1] ^= rotate( x[0]+ x[3],  7);
   x[2] ^= rotate( x[1]+ x[0],  9);
   x[3] ^= rotate( x[2]+ x[1], 13);
   x[0] ^= rotate( x[3]+ x[2], 18);

   x[6] ^= rotate( x[5]+ x[4],  7);
   x[7] ^= rotate( x[6]+ x[5],  9);
   x[4] ^= rotate( x[7]+ x[6], 13);
   x[5] ^= rotate( x[4]+ x[7], 18);

  x[11] ^= rotate(x[10]+ x[9],  7);
   x[8] ^= rotate(x[11]+x[10],  9);
   x[9] ^= rotate( x[8]+x[11], 13);
  x[10] ^= rotate( x[9]+ x[8], 18);

  x[12] ^= rotate(x[15]+x[14],  7);
  x[13] ^= rotate(x[12]+x[15],  9);
  x[14] ^= rotate(x[13]+x[12], 13);
  x[15] ^= rotate(x[14]+x[13], 18);
   x[4] ^= rotate( x[0]+x[12],  7);
   x[8] ^= rotate( x[4]+ x[0],  9);
  x[12] ^= rotate( x[8]+ x[4], 13);
   x[0] ^= rotate(x[12]+ x[8], 18);

   x[9] ^= rotate( x[5]+ x[1],  7);
  x[13] ^= rotate( x[9]+ x[5],  9);
   x[1] ^= rotate(x[13]+ x[9], 13);
   x[5] ^= rotate( x[1]+x[13], 18);

  x[14] ^= rotate(x[10]+ x[6],  7);
   x[2] ^= rotate(x[14]+x[10],  9);
   x[6] ^= rotate( x[2]+x[14], 13);
  x[10] ^= rotate( x[6]+ x[2], 18);

   x[3] ^= rotate(x[15]+x[11],  7);
   x[7] ^= rotate( x[3]+x[15],  9);
  x[11] ^= rotate( x[7]+ x[3], 13);
  x[15] ^= rotate(x[11]+ x[7], 18);

   x[1] ^= rotate( x[0]+ x[3],  7);
   x[2] ^= rotate( x[1]+ x[0],  9);
   x[3] ^= rotate( x[2]+ x[1], 13);
   x[0] ^= rotate( x[3]+ x[2], 18);

   x[6] ^= rotate( x[5]+ x[4],  7);
   x[7] ^= rotate( x[6]+ x[5],  9);
   x[4] ^= rotate( x[7]+ x[6], 13);
   x[5] ^= rotate( x[4]+ x[7], 18);

  x[11] ^= rotate(x[10]+ x[9],  7);
   x[8] ^= rotate(x[11]+x[10],  9);
   x[9] ^= rotate( x[8]+x[11], 13);
  x[10] ^= rotate( x[9]+ x[8], 18);

  x[12] ^= rotate(x[15]+x[14],  7);
  x[13] ^= rotate(x[12]+x[15],  9);
  x[14] ^= rotate(x[13]+x[12], 13);
  x[15] ^= rotate(x[14]+x[13], 18);
   x[4] ^= rotate( x[0]+x[12],  7);
   x[8] ^= rotate( x[4]+ x[0],  9);
  x[12] ^= rotate( x[8]+ x[4], 13);
   x[0] ^= rotate(x[12]+ x[8], 18);

   x[9] ^= rotate( x[5]+ x[1],  7);
  x[13] ^= rotate( x[9]+ x[5],  9);
   x[1] ^= rotate(x[13]+ x[9], 13);
   x[5] ^= rotate( x[1]+x[13], 18);

  x[14] ^= rotate(x[10]+ x[6],  7);
   x[2] ^= rotate(x[14]+x[10],  9);
   x[6] ^= rotate( x[2]+x[14], 13);
  x[10] ^= rotate( x[6]+ x[2], 18);

   x[3] ^= rotate(x[15]+x[11],  7);
   x[7] ^= rotate( x[3]+x[15],  9);
  x[11] ^= rotate( x[7]+ x[3], 13);
  x[15] ^= rotate(x[11]+ x[7], 18);

   x[1] ^= rotate( x[0]+ x[3],  7);
   x[2] ^= rotate( x[1]+ x[0],  9);
   x[3] ^= rotate( x[2]+ x[1], 13);
   x[0] ^= rotate( x[3]+ x[2], 18);

   x[6] ^= rotate( x[5]+ x[4],  7);
   x[7] ^= rotate( x[6]+ x[5],  9);
   x[4] ^= rotate( x[7]+ x[6], 13);
   x[5] ^= rotate( x[4]+ x[7], 18);

  x[11] ^= rotate(x[10]+ x[9],  7);
   x[8] ^= rotate(x[11]+x[10],  9);
   x[9] ^= rotate( x[8]+x[11], 13);
  x[10] ^= rotate( x[9]+ x[8], 18);

  x[12] ^= rotate(x[15]+x[14],  7);
  x[13] ^= rotate(x[12]+x[15],  9);
  x[14] ^= rotate(x[13]+x[12], 13);
  x[15] ^= rotate(x[14]+x[13], 18);
   x[4] ^= rotate( x[0]+x[12],  7);
   x[8] ^= rotate( x[4]+ x[0],  9);
  x[12] ^= rotate( x[8]+ x[4], 13);
   x[0] ^= rotate(x[12]+ x[8], 18);

   x[9] ^= rotate( x[5]+ x[1],  7);
  x[13] ^= rotate( x[9]+ x[5],  9);
   x[1] ^= rotate(x[13]+ x[9], 13);
   x[5] ^= rotate( x[1]+x[13], 18);

  x[14] ^= rotate(x[10]+ x[6],  7);
   x[2] ^= rotate(x[14]+x[10],  9);
   x[6] ^= rotate( x[2]+x[14], 13);
  x[10] ^= rotate( x[6]+ x[2], 18);

   x[3] ^= rotate(x[15]+x[11],  7);
   x[7] ^= rotate( x[3]+x[15],  9);
  x[11] ^= rotate( x[7]+ x[3], 13);
  x[15] ^= rotate(x[11]+ x[7], 18);

   x[1] ^= rotate( x[0]+ x[3],  7);
   x[2] ^= rotate( x[1]+ x[0],  9);
   x[3] ^= rotate( x[2]+ x[1], 13);
   x[0] ^= rotate( x[3]+ x[2], 18);

   x[6] ^= rotate( x[5]+ x[4],  7);
   x[7] ^= rotate( x[6]+ x[5],  9);
   x[4] ^= rotate( x[7]+ x[6], 13);
   x[5] ^= rotate( x[4]+ x[7], 18);

  x[11] ^= rotate(x[10]+ x[9],  7);
   x[8] ^= rotate(x[11]+x[10],  9);
   x[9] ^= rotate( x[8]+x[11], 13);
  x[10] ^= rotate( x[9]+ x[8], 18);

  x[12] ^= rotate(x[15]+x[14],  7);
  x[13] ^= rotate(x[12]+x[15],  9);
  x[14] ^= rotate(x[13]+x[12], 13);
  x[15] ^= rotate(x[14]+x[13], 18);
   x[4] ^= rotate( x[0]+x[12],  7);
   x[8] ^= rotate( x[4]+ x[0],  9);
  x[12] ^= rotate( x[8]+ x[4], 13);
   x[0] ^= rotate(x[12]+ x[8], 18);

   x[9] ^= rotate( x[5]+ x[1],  7);
  x[13] ^= rotate( x[9]+ x[5],  9);
   x[1] ^= rotate(x[13]+ x[9], 13);
   x[5] ^= rotate( x[1]+x[13], 18);

  x[14] ^= rotate(x[10]+ x[6],  7);
   x[2] ^= rotate(x[14]+x[10],  9);
   x[6] ^= rotate( x[2]+x[14], 13);
  x[10] ^= rotate( x[6]+ x[2], 18);

   x[3] ^= rotate(x[15]+x[11],  7);
   x[7] ^= rotate( x[3]+x[15],  9);
  x[11] ^= rotate( x[7]+ x[3], 13);
  x[15] ^= rotate(x[11]+ x[7], 18);

   x[1] ^= rotate( x[0]+ x[3],  7);
   x[2] ^= rotate( x[1]+ x[0],  9);
   x[3] ^= rotate( x[2]+ x[1], 13);
   x[0] ^= rotate( x[3]+ x[2], 18);

   x[6] ^= rotate( x[5]+ x[4],  7);
   x[7] ^= rotate( x[6]+ x[5],  9);
   x[4] ^= rotate( x[7]+ x[6], 13);
   x[5] ^= rotate( x[4]+ x[7], 18);

  x[11] ^= rotate(x[10]+ x[9],  7);
   x[8] ^= rotate(x[11]+x[10],  9);
   x[9] ^= rotate( x[8]+x[11], 13);
  x[10] ^= rotate( x[9]+ x[8], 18);

  x[12] ^= rotate(x[15]+x[14],  7);
  x[13] ^= rotate(x[12]+x[15],  9);
  x[14] ^= rotate(x[13]+x[12], 13);
  x[15] ^= rotate(x[14]+x[13], 18);
   x[4] ^= rotate( x[0]+x[12],  7);
   x[8] ^= rotate( x[4]+ x[0],  9);
  x[12] ^= rotate( x[8]+ x[4], 13);
   x[0] ^= rotate(x[12]+ x[8], 18);

   x[9] ^= rotate( x[5]+ x[1],  7);
  x[13] ^= rotate( x[9]+ x[5],  9);
   x[1] ^= rotate(x[13]+ x[9], 13);
   x[5] ^= rotate( x[1]+x[13], 18);

  x[14] ^= rotate(x[10]+ x[6],  7);
   x[2] ^= rotate(x[14]+x[10],  9);
   x[6] ^= rotate( x[2]+x[14], 13);
  x[10] ^= rotate( x[6]+ x[2], 18);

   x[3] ^= rotate(x[15]+x[11],  7);
   x[7] ^= rotate( x[3]+x[15],  9);
  x[11] ^= rotate( x[7]+ x[3], 13);
  x[15] ^= rotate(x[11]+ x[7], 18);

   x[1] ^= rotate( x[0]+ x[3],  7);
   x[2] ^= rotate( x[1]+ x[0],  9);
   x[3] ^= rotate( x[2]+ x[1], 13);
   x[0] ^= rotate( x[3]+ x[2], 18);

   x[6] ^= rotate( x[5]+ x[4],  7);
   x[7] ^= rotate( x[6]+ x[5],  9);
   x[4] ^= rotate( x[7]+ x[6], 13);
   x[5] ^= rotate( x[4]+ x[7], 18);

  x[11] ^= rotate(x[10]+ x[9],  7);
   x[8] ^= rotate(x[11]+x[10],  9);
   x[9] ^= rotate( x[8]+x[11], 13);
  x[10] ^= rotate( x[9]+ x[8], 18);

  x[12] ^= rotate(x[15]+x[14],  7);
  x[13] ^= rotate(x[12]+x[15],  9);
  x[14] ^= rotate(x[13]+x[12], 13);
  x[15] ^= rotate(x[14]+x[13], 18);
   x[4] ^= rotate( x[0]+x[12],  7);
   x[8] ^= rotate( x[4]+ x[0],  9);
  x[12] ^= rotate( x[8]+ x[4], 13);
   x[0] ^= rotate(x[12]+ x[8], 18);

   x[9] ^= rotate( x[5]+ x[1],  7);
  x[13] ^= rotate( x[9]+ x[5],  9);
   x[1] ^= rotate(x[13]+ x[9], 13);
   x[5] ^= rotate( x[1]+x[13], 18);

  x[14] ^= rotate(x[10]+ x[6],  7);
   x[2] ^= rotate(x[14]+x[10],  9);
   x[6] ^= rotate( x[2]+x[14], 13);
  x[10] ^= rotate( x[6]+ x[2], 18);

   x[3] ^= rotate(x[15]+x[11],  7);
   x[7] ^= rotate( x[3]+x[15],  9);
  x[11] ^= rotate( x[7]+ x[3], 13);
  x[15] ^= rotate(x[11]+ x[7], 18);

   x[1] ^= rotate( x[0]+ x[3],  7);
   x[2] ^= rotate( x[1]+ x[0],  9);
   x[3] ^= rotate( x[2]+ x[1], 13);
   x[0] ^= rotate( x[3]+ x[2], 18);

   x[6] ^= rotate( x[5]+ x[4],  7);
   x[7] ^= rotate( x[6]+ x[5],  9);
   x[4] ^= rotate( x[7]+ x[6], 13);
   x[5] ^= rotate( x[4]+ x[7], 18);

  x[11] ^= rotate(x[10]+ x[9],  7);
   x[8] ^= rotate(x[11]+x[10],  9);
   x[9] ^= rotate( x[8]+x[11], 13);
  x[10] ^= rotate( x[9]+ x[8], 18);

  x[12] ^= rotate(x[15]+x[14],  7);
  x[13] ^= rotate(x[12]+x[15],  9);
  x[14] ^= rotate(x[13]+x[12], 13);
  x[15] ^= rotate(x[14]+x[13], 18);
   x[4] ^= rotate( x[0]+x[12],  7);
   x[8] ^= rotate( x[4]+ x[0],  9);
  x[12] ^= rotate( x[8]+ x[4], 13);
   x[0] ^= rotate(x[12]+ x[8], 18);

   x[9] ^= rotate( x[5]+ x[1],  7);
  x[13] ^= rotate( x[9]+ x[5],  9);
   x[1] ^= rotate(x[13]+ x[9], 13);
   x[5] ^= rotate( x[1]+x[13], 18);

  x[14] ^= rotate(x[10]+ x[6],  7);
   x[2] ^= rotate(x[14]+x[10],  9);
   x[6] ^= rotate( x[2]+x[14], 13);
  x[10] ^= rotate( x[6]+ x[2], 18);

   x[3] ^= rotate(x[15]+x[11],  7);
   x[7] ^= rotate( x[3]+x[15],  9);
  x[11] ^= rotate( x[7]+ x[3], 13);
  x[15] ^= rotate(x[11]+ x[7], 18);

   x[1] ^= rotate( x[0]+ x[3],  7);
   x[2] ^= rotate( x[1]+ x[0],  9);
   x[3] ^= rotate( x[2]+ x[1], 13);
   x[0] ^= rotate( x[3]+ x[2], 18);

   x[6] ^= rotate( x[5]+ x[4],  7);
   x[7] ^= rotate( x[6]+ x[5],  9);
   x[4] ^= rotate( x[7]+ x[6], 13);
   x[5] ^= rotate( x[4]+ x[7], 18);

  x[11] ^= rotate(x[10]+ x[9],  7);
   x[8] ^= rotate(x[11]+x[10],  9);
   x[9] ^= rotate( x[8]+x[11], 13);
  x[10] ^= rotate( x[9]+ x[8], 18);

  x[12] ^= rotate(x[15]+x[14],  7);
  x[13] ^= rotate(x[12]+x[15],  9);
  x[14] ^= rotate(x[13]+x[12], 13);
  x[15] ^= rotate(x[14]+x[13], 18);
   x[4] ^= rotate( x[0]+x[12],  7);
   x[8] ^= rotate( x[4]+ x[0],  9);
  x[12] ^= rotate( x[8]+ x[4], 13);
   x[0] ^= rotate(x[12]+ x[8], 18);

   x[9] ^= rotate( x[5]+ x[1],  7);
  x[13] ^= rotate( x[9]+ x[5],  9);
   x[1] ^= rotate(x[13]+ x[9], 13);
   x[5] ^= rotate( x[1]+x[13], 18);

  x[14] ^= rotate(x[10]+ x[6],  7);
   x[2] ^= rotate(x[14]+x[10],  9);
   x[6] ^= rotate( x[2]+x[14], 13);
  x[10] ^= rotate( x[6]+ x[2], 18);

   x[3] ^= rotate(x[15]+x[11],  7);
   x[7] ^= rotate( x[3]+x[15],  9);
  x[11] ^= rotate( x[7]+ x[3], 13);
  x[15] ^= rotate(x[11]+ x[7], 18);

   x[1] ^= rotate( x[0]+ x[3],  7);
   x[2] ^= rotate( x[1]+ x[0],  9);
   x[3] ^= rotate( x[2]+ x[1], 13);
   x[0] ^= rotate( x[3]+ x[2], 18);

   x[6] ^= rotate( x[5]+ x[4],  7);
   x[7] ^= rotate( x[6]+ x[5],  9);
   x[4] ^= rotate( x[7]+ x[6], 13);
   x[5] ^= rotate( x[4]+ x[7], 18);

  x[11] ^= rotate(x[10]+ x[9],  7);
   x[8] ^= rotate(x[11]+x[10],  9);
   x[9] ^= rotate( x[8]+x[11], 13);
  x[10] ^= rotate( x[9]+ x[8], 18);

  x[12] ^= rotate(x[15]+x[14],  7);
  x[13] ^= rotate(x[12]+x[15],  9);
  x[14] ^= rotate(x[13]+x[12], 13);
  x[15] ^= rotate(x[14]+x[13], 18);
   x[4] ^= rotate( x[0]+x[12],  7);
   x[8] ^= rotate( x[4]+ x[0],  9);
  x[12] ^= rotate( x[8]+ x[4], 13);
   x[0] ^= rotate(x[12]+ x[8], 18);

   x[9] ^= rotate( x[5]+ x[1],  7);
  x[13] ^= rotate( x[9]+ x[5],  9);
   x[1] ^= rotate(x[13]+ x[9], 13);
   x[5] ^= rotate( x[1]+x[13], 18);

  x[14] ^= rotate(x[10]+ x[6],  7);
   x[2] ^= rotate(x[14]+x[10],  9);
   x[6] ^= rotate( x[2]+x[14], 13);
  x[10] ^= rotate( x[6]+ x[2], 18);

   x[3] ^= rotate(x[15]+x[11],  7);
   x[7] ^= rotate( x[3]+x[15],  9);
  x[11] ^= rotate( x[7]+ x[3], 13);
  x[15] ^= rotate(x[11]+ x[7], 18);

   x[1] ^= rotate( x[0]+ x[3],  7);
   x[2] ^= rotate( x[1]+ x[0],  9);
   x[3] ^= rotate( x[2]+ x[1], 13);
   x[0] ^= rotate( x[3]+ x[2], 18);

   x[6] ^= rotate( x[5]+ x[4],  7);
   x[7] ^= rotate( x[6]+ x[5],  9);
   x[4] ^= rotate( x[7]+ x[6], 13);
   x[5] ^= rotate( x[4]+ x[7], 18);

  x[11] ^= rotate(x[10]+ x[9],  7);
   x[8] ^= rotate(x[11]+x[10],  9);
   x[9] ^= rotate( x[8]+x[11], 13);
  x[10] ^= rotate( x[9]+ x[8], 18);

  x[12] ^= rotate(x[15]+x[14],  7);
  x[13] ^= rotate(x[12]+x[15],  9);
  x[14] ^= rotate(x[13]+x[12], 13);
  x[15] ^= rotate(x[14]+x[13], 18);
}

// Helper macros for salsavi_load
#define load(X) \
  (v8u)(*((uint32_t*)(X)))
#define H(x) ((uint32_t)(((x) >> 32) & 0xffffffff))
#define L(x) ((uint32_t)((x) & 0xffffffff))
static inline void salsavi_load(v8u* x,
                                const uint8_t* k,
                                const uint8_t* n,
                                const uint64_t c) {
  x[0]  = load(salsa_sigma + 0);
  x[5]  = load(salsa_sigma + 4);
  x[10] = load(salsa_sigma + 8);
  x[15] = load(salsa_sigma + 12);

  x[1]  = load(k + 0);
  x[2]  = load(k + 4);
  x[3]  = load(k + 8);
  x[4]  = load(k + 12);

  x[11] = load(k + 16);
  x[12] = load(k + 20);
  x[13] = load(k + 24);
  x[14] = load(k + 28);

  x[6]  = load(n + 0);
  x[7]  = load(n + 4);
//  x[8]  = load(n + 8);
  x[8]  = (v8u){H(c + 0), H(c + 1), H(c + 2), H(c + 3),
                H(c + 4), H(c + 5), H(c + 6), H(c + 7)};
  x[9]  = (v8u){L(c + 0), L(c + 1), L(c + 2), L(c + 3),
                L(c + 4), L(c + 5), L(c + 6), L(c + 7)};
//  v8u x9  = load(in + 12);
}
#undef load
#undef H
#undef L

static inline void salsavi8(v8u* io,
                            const uint8_t* kn,
                            const uint64_t counter) {
  v8u in[16];
  v8u x[16];
  salsavi_load(in, kn, kn+32, counter);
  x[0] = in[0];
  x[1] = in[1];
  x[2] = in[2];
  x[3] = in[3];
  x[4] = in[4];
  x[5] = in[5];
  x[6] = in[6];
  x[7] = in[7];
  x[8] = in[8];
  x[9] = in[9];
  x[10] = in[10];
  x[11] = in[11];
  x[12] = in[12];
  x[13] = in[13];
  x[14] = in[14];
  x[15] = in[15];
  hsalsa_core(x);
  x[0] += in[0];
  x[1] += in[1];
  x[2] += in[2];
  x[3] += in[3];
  x[4] += in[4];
  x[5] += in[5];
  x[6] += in[6];
  x[7] += in[7];
  x[8] += in[8];
  x[9] += in[9];
  x[10] += in[10];
  x[11] += in[11];
  x[12] += in[12];
  x[13] += in[13];
  x[14] += in[14];
  x[15] += in[15];
  io[0] ^= x[0];
  io[1] ^= x[1];
  io[2] ^= x[2];
  io[3] ^= x[3];
  io[4] ^= x[4];
  io[5] ^= x[5];
  io[6] ^= x[6];
  io[7] ^= x[7];
  io[8] ^= x[8];
  io[9] ^= x[9];
  io[10] ^= x[10];
  io[11] ^= x[11];
  io[12] ^= x[12];
  io[13] ^= x[13];
  io[14] ^= x[14];
  io[15] ^= x[15];
}

static inline void vi8_reorder(void* _out, v8u* in) {
  uint32_t* out = (uint32_t*)_out;
  out[0*16 + 0] = in[0][0];
  out[0*16 + 1] = in[1][0];
  out[0*16 + 2] = in[2][0];
  out[0*16 + 3] = in[3][0];
  out[0*16 + 4] = in[4][0];
  out[0*16 + 5] = in[5][0];
  out[0*16 + 6] = in[6][0];
  out[0*16 + 7] = in[7][0];
  out[0*16 + 8] = in[8][0];
  out[0*16 + 9] = in[9][0];
  out[0*16 + 10] = in[10][0];
  out[0*16 + 11] = in[11][0];
  out[0*16 + 12] = in[12][0];
  out[0*16 + 13] = in[13][0];
  out[0*16 + 14] = in[14][0];
  out[0*16 + 15] = in[15][0];
  out[1*16 + 0] = in[0][1];
  out[1*16 + 1] = in[1][1];
  out[1*16 + 2] = in[2][1];
  out[1*16 + 3] = in[3][1];
  out[1*16 + 4] = in[4][1];
  out[1*16 + 5] = in[5][1];
  out[1*16 + 6] = in[6][1];
  out[1*16 + 7] = in[7][1];
  out[1*16 + 8] = in[8][1];
  out[1*16 + 9] = in[9][1];
  out[1*16 + 10] = in[10][1];
  out[1*16 + 11] = in[11][1];
  out[1*16 + 12] = in[12][1];
  out[1*16 + 13] = in[13][1];
  out[1*16 + 14] = in[14][1];
  out[1*16 + 15] = in[15][1];
  out[2*16 + 0] = in[0][2];
  out[2*16 + 1] = in[1][2];
  out[2*16 + 2] = in[2][2];
  out[2*16 + 3] = in[3][2];
  out[2*16 + 4] = in[4][2];
  out[2*16 + 5] = in[5][2];
  out[2*16 + 6] = in[6][2];
  out[2*16 + 7] = in[7][2];
  out[2*16 + 8] = in[8][2];
  out[2*16 + 9] = in[9][2];
  out[2*16 + 10] = in[10][2];
  out[2*16 + 11] = in[11][2];
  out[2*16 + 12] = in[12][2];
  out[2*16 + 13] = in[13][2];
  out[2*16 + 14] = in[14][2];
  out[2*16 + 15] = in[15][2];
  out[3*16 + 0] = in[0][3];
  out[3*16 + 1] = in[1][3];
  out[3*16 + 2] = in[2][3];
  out[3*16 + 3] = in[3][3];
  out[3*16 + 4] = in[4][3];
  out[3*16 + 5] = in[5][3];
  out[3*16 + 6] = in[6][3];
  out[3*16 + 7] = in[7][3];
  out[3*16 + 8] = in[8][3];
  out[3*16 + 9] = in[9][3];
  out[3*16 + 10] = in[10][3];
  out[3*16 + 11] = in[11][3];
  out[3*16 + 12] = in[12][3];
  out[3*16 + 13] = in[13][3];
  out[3*16 + 14] = in[14][3];
  out[3*16 + 15] = in[15][3];
  out[4*16 + 0] = in[0][4];
  out[4*16 + 1] = in[1][4];
  out[4*16 + 2] = in[2][4];
  out[4*16 + 3] = in[3][4];
  out[4*16 + 4] = in[4][4];
  out[4*16 + 5] = in[5][4];
  out[4*16 + 6] = in[6][4];
  out[4*16 + 7] = in[7][4];
  out[4*16 + 8] = in[8][4];
  out[4*16 + 9] = in[9][4];
  out[4*16 + 10] = in[10][4];
  out[4*16 + 11] = in[11][4];
  out[4*16 + 12] = in[12][4];
  out[4*16 + 13] = in[13][4];
  out[4*16 + 14] = in[14][4];
  out[4*16 + 15] = in[15][4];
  out[5*16 + 0] = in[0][5];
  out[5*16 + 1] = in[1][5];
  out[5*16 + 2] = in[2][5];
  out[5*16 + 3] = in[3][5];
  out[5*16 + 4] = in[4][5];
  out[5*16 + 5] = in[5][5];
  out[5*16 + 6] = in[6][5];
  out[5*16 + 7] = in[7][5];
  out[5*16 + 8] = in[8][5];
  out[5*16 + 9] = in[9][5];
  out[5*16 + 10] = in[10][5];
  out[5*16 + 11] = in[11][5];
  out[5*16 + 12] = in[12][5];
  out[5*16 + 13] = in[13][5];
  out[5*16 + 14] = in[14][5];
  out[5*16 + 15] = in[15][5];
  out[6*16 + 0] = in[0][6];
  out[6*16 + 1] = in[1][6];
  out[6*16 + 2] = in[2][6];
  out[6*16 + 3] = in[3][6];
  out[6*16 + 4] = in[4][6];
  out[6*16 + 5] = in[5][6];
  out[6*16 + 6] = in[6][6];
  out[6*16 + 7] = in[7][6];
  out[6*16 + 8] = in[8][6];
  out[6*16 + 9] = in[9][6];
  out[6*16 + 10] = in[10][6];
  out[6*16 + 11] = in[11][6];
  out[6*16 + 12] = in[12][6];
  out[6*16 + 13] = in[13][6];
  out[6*16 + 14] = in[14][6];
  out[6*16 + 15] = in[15][6];
  out[7*16 + 0] = in[0][7];
  out[7*16 + 1] = in[1][7];
  out[7*16 + 2] = in[2][7];
  out[7*16 + 3] = in[3][7];
  out[7*16 + 4] = in[4][7];
  out[7*16 + 5] = in[5][7];
  out[7*16 + 6] = in[6][7];
  out[7*16 + 7] = in[7][7];
  out[7*16 + 8] = in[8][7];
  out[7*16 + 9] = in[9][7];
  out[7*16 + 10] = in[10][7];
  out[7*16 + 11] = in[11][7];
  out[7*16 + 12] = in[12][7];
  out[7*16 + 13] = in[13][7];
  out[7*16 + 14] = in[14][7];
  out[7*16 + 15] = in[15][7];
}

// TODO(dlg): Test against Salsa ref.

static inline void salsavi8x128(void* _io, const uint8_t* kn) {
  v8u* io = (v8u*)_io;
  uint64_t counter = 0;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
  salsavi8(io, kn, counter); io += 16; counter += 8;
}

static inline void hash_block(uint8_t* tag,
                              const void* in,
                              const uint8_t* key) {
  blake2b_state s;
  blake2b_init_key(&s, 64, key, KEYLEN);
  blake2b_update(&s, in, BLOCKLEN);
  blake2b_final(&s, tag, TAGLEN);
}

static inline void block_encrypt(uint8_t* tag,
                                 void* _io,
                                 const uint8_t* key) {
  salsavi8x128(_io, key);
  hash_block(tag, _io, key);
}

static inline int block_decrypt(void* out,
                                const uint8_t* tag,
                                const void* in,
                                const uint8_t* key) {
  uint8_t ptag[TAGLEN] = {0};
  hash_block(ptag, in, key);
  int err = memcompare(ptag, tag, TAGLEN);
  if (err != 0) { return err; }
  memcpy(out, in, BLOCKLEN);
  salsavi8x128(out, key);
  return 0;
}

/** Derive the 40B block key.
 *
 * @param key[out]     The derived key, KEYLEN bytes.
 * @param gkn[in]      The global key+nonce, GKNLEN bytes.
 * @param blocknum[in] The block number.
 * @param blockgen[in] The block generation.
 */
static inline void block_kdf(uint8_t* key,
                             const uint8_t* gkn,
                             const uint64_t blocknum,
                             const uint64_t blockgen) {
  blake2b_state s;
  blake2b_init_key(&s, 64, gkn, GKNLEN);
  blake2b_update(&s, (uint8_t*)&blockgen, 8);
  blake2b_update(&s, (uint8_t*)&blocknum, 8);
  blake2b_final(&s, key, KEYLEN);
}

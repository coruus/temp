#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#define cycles __builtin_readcyclecounter


typedef struct {
  uint64_t can0[4];
  uint64_t A[25];
  uint64_t C[5];
  uint64_t Cp[4];
  uint64_t D[8];
  uint64_t canN[4];
} state;

extern uint64_t theta(void*);

#define N (1ULL << 20ULL)
#define FN theta

void printstate(state s) {
  for (int i = 0; i < 25; i++) {
    !(i % 5) && printf("\nA%2u ", i);
    printf("%016llx ", s.A[i]);
  }
  printf("\nC   ");
  for (int i = 0; i < 5; i++) {
    printf("%016llx ", s.C[i]);
  }
  printf("\nC'  ");
  for (int i = 0; i < 4; i++) {
    printf("%016llx ", s.Cp[i]);
  }
  printf("\nD   ");
  for (int i = 0; i < 5; i++) {
    printf("%016llx ", s.D[i]);
  }
}

static inline uint64_t rol(uint64_t x, uint8_t s) {
  if ((s % 64) == 0) {
    return x;
  }
  return (x << s) ^ (x >> (64 - s));
}

static const uint8_t rhol[25] = { 
  0, 1, 62, 28, 27,
  36, 44, 6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21, 8,
  18, 2, 61, 56, 14 };

void rho_ref(state* s) {
  for (int i = 0; i < 25; i++) {
    s->A[i] = rol(s->A[i], rhol[i]);
  }
}

void theta_ref(state* s) {
  for (int x = 0; x < 5; x++) {
    s->C[x] = 0;
    for (int y = 0; y < 25; y += 5) {
      s->C[x] ^= s->A[x + y];
    }
  }
  for (int x = 0; x < 5; x++) {
    s->D[x] = s->C[(x+4)%5] ^ rol(s->C[(x+1)%5], 1);
  }
  //memcpy(&(s->Cp), &(s->C), 3 * 8);
  for (int x = 0; x < 5; x++) {
    for (int y = 0; y < 25; y += 5) {
      s->A[x + y] ^= s->D[x];
    }
  }
}

extern void keccakf(void*);

int main(void) {
  state s, sref;
  memset(&s, 0, sizeof(s));
  for (int i = 0; i < 200; i++) {
    ((uint8_t*)s.A)[i] = i;
  }
  memcpy(&sref, &s, sizeof(state));

  printf("ref\n");
  theta_ref(&sref);
  rho_ref(&sref);
  printstate(sref);
  printf("\nasm");
  uint64_t c = theta(&(s.A));
  //kck(&(s.A));
  printstate(s);

  uint64_t a[25] = {0};
  uint64_t kscyc = cycles();
  for (uint64_t i = 0; i < N; i++) {
    keccakf(a);
  }
  kscyc = cycles() - kscyc;
  double cpi = (double)kscyc / (double)N;
  printf("\nk.s: %llu, %f, %f\n", kscyc, cpi, cpi / 200.0);

  printf("\ncycles=%llu\n", c);
  double cycles = 0;
  uint64_t min = SIZE_MAX;
  for (uint64_t i = 0; i < N; i++) {
    uint64_t cyc = FN(&s);
    cycles += cyc;
    min = (cyc < min) ? cyc : min;
  }
  printf("theta: avg=%f,min=%llu\n,cpb=%f", 24 * cycles / (double)(N), 24 * min,
      cycles / (double)N / 8.333333);
  return 0;
}

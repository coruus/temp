/* Fully unrolled Keccak-f[1600] permutation operating on a vector
   of 4 Keccak states.

   Designers: Guido Bertoni, Joan Daemen, Michael Peeters,
              and Gilles Van Assche.

   Derived from
   github.com/gvanas/KeccakCodePackage/Optimized/KeccakF-1600-opt64.c
   @c4f93b469a105b618942f032150793d7dccc7edf

   (This is a preprocessed, reformatted, and lightly edited version
   with UseLaneComplementing not defined.)

  Editor: David Leon Gil

   License: CC0 (http://creativecommons.org/publicdomain/zero/1.0/)
*/
#include <stdint.h>
#include <stdlib.h>

#define ROL64(a, offset) \
  ((((u64v)(a)) << (offset)) ^ (((u64v)(a)) >> (64 - (offset))))
#define VW 4

typedef uint64_t u64v __attribute__((ext_vector_type(VW)));

static const uint64_t round_constants[24] = {0x0000000000000001ULL,
                                             0x0000000000008082ULL,
                                             0x800000000000808aULL,
                                             0x8000000080008000ULL,
                                             0x000000000000808bULL,
                                             0x0000000080000001ULL,
                                             0x8000000080008081ULL,
                                             0x8000000000008009ULL,
                                             0x000000000000008aULL,
                                             0x0000000000000088ULL,
                                             0x0000000080008009ULL,
                                             0x000000008000000aULL,
                                             0x000000008000808bULL,
                                             0x800000000000008bULL,
                                             0x8000000000008089ULL,
                                             0x8000000000008003ULL,
                                             0x8000000000008002ULL,
                                             0x8000000000000080ULL,
                                             0x000000000000800aULL,
                                             0x800000008000000aULL,
                                             0x8000000080008081ULL,
                                             0x8000000000008080ULL,
                                             0x0000000080000001ULL,
                                             0x8000000080008008ULL};


void keccakfv4(void* state) {
  u64v Aba, Abe, Abi, Abo, Abu;
  u64v Aga, Age, Agi, Ago, Agu;
  u64v Aka, Ake, Aki, Ako, Aku;
  u64v Ama, Ame, Ami, Amo, Amu;
  u64v Asa, Ase, Asi, Aso, Asu;
  u64v Bba, Bbe, Bbi, Bbo, Bbu;
  u64v Bga, Bge, Bgi, Bgo, Bgu;
  u64v Bka, Bke, Bki, Bko, Bku;
  u64v Bma, Bme, Bmi, Bmo, Bmu;
  u64v Bsa, Bse, Bsi, Bso, Bsu;
  u64v Ca, Ce, Ci, Co, Cu;
  u64v Da, De, Di, Do, Du;
  u64v Eba, Ebe, Ebi, Ebo, Ebu;
  u64v Ega, Ege, Egi, Ego, Egu;
  u64v Eka, Eke, Eki, Eko, Eku;
  u64v Ema, Eme, Emi, Emo, Emu;
  u64v Esa, Ese, Esi, Eso, Esu;

  u64v* stateAsLanes = (u64v*)state;

  Aba = stateAsLanes[0];
  Abe = stateAsLanes[1];
  Abi = stateAsLanes[2];
  Abo = stateAsLanes[3];
  Abu = stateAsLanes[4];
  Aga = stateAsLanes[5];
  Age = stateAsLanes[6];
  Agi = stateAsLanes[7];
  Ago = stateAsLanes[8];
  Agu = stateAsLanes[9];
  Aka = stateAsLanes[10];
  Ake = stateAsLanes[11];
  Aki = stateAsLanes[12];
  Ako = stateAsLanes[13];
  Aku = stateAsLanes[14];
  Ama = stateAsLanes[15];
  Ame = stateAsLanes[16];
  Ami = stateAsLanes[17];
  Amo = stateAsLanes[18];
  Amu = stateAsLanes[19];
  Asa = stateAsLanes[20];
  Ase = stateAsLanes[21];
  Asi = stateAsLanes[22];
  Aso = stateAsLanes[23];
  Asu = stateAsLanes[24];
  Ca = Aba ^ Aga ^ Aka ^ Ama ^ Asa;
  Ce = Abe ^ Age ^ Ake ^ Ame ^ Ase;
  Ci = Abi ^ Agi ^ Aki ^ Ami ^ Asi;
  Co = Abo ^ Ago ^ Ako ^ Amo ^ Aso;
  Cu = Abu ^ Agu ^ Aku ^ Amu ^ Asu;
  for (int i = 0; i < 24; i++) {
    Da = Cu ^ ((((u64v)Ce) << 1) ^ (((u64v)Ce) >> (64 - 1)));
    De = Ca ^ ((((u64v)Ci) << 1) ^ (((u64v)Ci) >> (64 - 1)));
    Di = Ce ^ ((((u64v)Co) << 1) ^ (((u64v)Co) >> (64 - 1)));
    Do = Ci ^ ((((u64v)Cu) << 1) ^ (((u64v)Cu) >> (64 - 1)));
    Du = Co ^ ((((u64v)Ca) << 1) ^ (((u64v)Ca) >> (64 - 1)));
    Aba ^= Da;
    Bba = Aba;
    Age ^= De;
    Bbe = ((((u64v)Age) << 44) ^ (((u64v)Age) >> (64 - 44)));
    Aki ^= Di;
    Bbi = ((((u64v)Aki) << 43) ^ (((u64v)Aki) >> (64 - 43)));
    Amo ^= Do;
    Bbo = ((((u64v)Amo) << 21) ^ (((u64v)Amo) >> (64 - 21)));
    Asu ^= Du;
    Bbu = ((((u64v)Asu) << 14) ^ (((u64v)Asu) >> (64 - 14)));
    Eba = Bba ^ ((~Bbe) & Bbi);
    Eba ^= round_constants[i];
    Ca = Eba;
    Ebe = Bbe ^ ((~Bbi) & Bbo);
    Ce = Ebe;
    Ebi = Bbi ^ ((~Bbo) & Bbu);
    Ci = Ebi;
    Ebo = Bbo ^ ((~Bbu) & Bba);
    Co = Ebo;
    Ebu = Bbu ^ ((~Bba) & Bbe);
    Cu = Ebu;
    Abo ^= Do;
    Bga = ((((u64v)Abo) << 28) ^ (((u64v)Abo) >> (64 - 28)));
    Agu ^= Du;
    Bge = ((((u64v)Agu) << 20) ^ (((u64v)Agu) >> (64 - 20)));
    Aka ^= Da;
    Bgi = ((((u64v)Aka) << 3) ^ (((u64v)Aka) >> (64 - 3)));
    Ame ^= De;
    Bgo = ((((u64v)Ame) << 45) ^ (((u64v)Ame) >> (64 - 45)));
    Asi ^= Di;
    Bgu = ((((u64v)Asi) << 61) ^ (((u64v)Asi) >> (64 - 61)));
    Ega = Bga ^ ((~Bge) & Bgi);
    Ca ^= Ega;
    Ege = Bge ^ ((~Bgi) & Bgo);
    Ce ^= Ege;
    Egi = Bgi ^ ((~Bgo) & Bgu);
    Ci ^= Egi;
    Ego = Bgo ^ ((~Bgu) & Bga);
    Co ^= Ego;
    Egu = Bgu ^ ((~Bga) & Bge);
    Cu ^= Egu;
    Abe ^= De;
    Bka = ((((u64v)Abe) << 1) ^ (((u64v)Abe) >> (64 - 1)));
    Agi ^= Di;
    Bke = ((((u64v)Agi) << 6) ^ (((u64v)Agi) >> (64 - 6)));
    Ako ^= Do;
    Bki = ((((u64v)Ako) << 25) ^ (((u64v)Ako) >> (64 - 25)));
    Amu ^= Du;
    Bko = ((((u64v)Amu) << 8) ^ (((u64v)Amu) >> (64 - 8)));
    Asa ^= Da;
    Bku = ((((u64v)Asa) << 18) ^ (((u64v)Asa) >> (64 - 18)));
    Eka = Bka ^ ((~Bke) & Bki);
    Ca ^= Eka;
    Eke = Bke ^ ((~Bki) & Bko);
    Ce ^= Eke;
    Eki = Bki ^ ((~Bko) & Bku);
    Ci ^= Eki;
    Eko = Bko ^ ((~Bku) & Bka);
    Co ^= Eko;
    Eku = Bku ^ ((~Bka) & Bke);
    Cu ^= Eku;
    Abu ^= Du;
    Bma = ((((u64v)Abu) << 27) ^ (((u64v)Abu) >> (64 - 27)));
    Aga ^= Da;
    Bme = ((((u64v)Aga) << 36) ^ (((u64v)Aga) >> (64 - 36)));
    Ake ^= De;
    Bmi = ((((u64v)Ake) << 10) ^ (((u64v)Ake) >> (64 - 10)));
    Ami ^= Di;
    Bmo = ((((u64v)Ami) << 15) ^ (((u64v)Ami) >> (64 - 15)));
    Aso ^= Do;
    Bmu = ((((u64v)Aso) << 56) ^ (((u64v)Aso) >> (64 - 56)));
    Ema = Bma ^ ((~Bme) & Bmi);
    Ca ^= Ema;
    Eme = Bme ^ ((~Bmi) & Bmo);
    Ce ^= Eme;
    Emi = Bmi ^ ((~Bmo) & Bmu);
    Ci ^= Emi;
    Emo = Bmo ^ ((~Bmu) & Bma);
    Co ^= Emo;
    Emu = Bmu ^ ((~Bma) & Bme);
    Cu ^= Emu;
    Abi ^= Di;
    Bsa = ((((u64v)Abi) << 62) ^ (((u64v)Abi) >> (64 - 62)));
    Ago ^= Do;
    Bse = ((((u64v)Ago) << 55) ^ (((u64v)Ago) >> (64 - 55)));
    Aku ^= Du;
    Bsi = ((((u64v)Aku) << 39) ^ (((u64v)Aku) >> (64 - 39)));
    Ama ^= Da;
    Bso = ((((u64v)Ama) << 41) ^ (((u64v)Ama) >> (64 - 41)));
    Ase ^= De;
    Bsu = ((((u64v)Ase) << 2) ^ (((u64v)Ase) >> (64 - 2)));
    Esa = Bsa ^ ((~Bse) & Bsi);
    Ca ^= Esa;
    Ese = Bse ^ ((~Bsi) & Bso);
    Ce ^= Ese;
    Esi = Bsi ^ ((~Bso) & Bsu);
    Ci ^= Esi;
    Eso = Bso ^ ((~Bsu) & Bsa);
    Co ^= Eso;
    Esu = Bsu ^ ((~Bsa) & Bse);
    Cu ^= Esu;
    Aba = Eba;
    Abe = Ebe;
    Abi = Ebi;
    Abo = Ebo;
    Abu = Ebu;
    Aga = Ega;
    Age = Ege;
    Agi = Egi;
    Ago = Ego;
    Agu = Egu;
    Aka = Eka;
    Ake = Eke;
    Aki = Eki;
    Ako = Eko;
    Aku = Eku;
    Ama = Ema;
    Ame = Eme;
    Ami = Emi;
    Amo = Emo;
    Amu = Emu;
    Asa = Esa;
    Ase = Ese;
    Asi = Esi;
    Aso = Eso;
    Asu = Esu;
  }
  stateAsLanes[0] = Aba;
  stateAsLanes[1] = Abe;
  stateAsLanes[2] = Abi;
  stateAsLanes[3] = Abo;
  stateAsLanes[4] = Abu;
  stateAsLanes[5] = Aga;
  stateAsLanes[6] = Age;
  stateAsLanes[7] = Agi;
  stateAsLanes[8] = Ago;
  stateAsLanes[9] = Agu;
  stateAsLanes[10] = Aka;
  stateAsLanes[11] = Ake;
  stateAsLanes[12] = Aki;
  stateAsLanes[13] = Ako;
  stateAsLanes[14] = Aku;
  stateAsLanes[15] = Ama;
  stateAsLanes[16] = Ame;
  stateAsLanes[17] = Ami;
  stateAsLanes[18] = Amo;
  stateAsLanes[19] = Amu;
  stateAsLanes[20] = Asa;
  stateAsLanes[21] = Ase;
  stateAsLanes[22] = Asi;
  stateAsLanes[23] = Aso;
  stateAsLanes[24] = Asu;
}

#if 1
#define cycles __builtin_readcyclecounter
#define N (1ULL << 22ULL)
#include <stdio.h>
int main(void) {
  u64v state[25] = {0};
  uint64_t start = cycles();
  for (uint64_t i = 0; i < N; i++) {
    keccakfv4(state);
  }
  double cpb = cycles() - start;
  printf("cycles = %f", cpb / N / VW);
  cpb /= (N * VW * (200 - 64));
  printf("state[0] = %llx\n", state[0][0] ^ state[0][1] ^ state[0][2] ^ state[0][3]);
  printf("cpb = %f\n", cpb);
}
#endif

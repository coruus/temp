#define STARTCOUNTER(NAME)                               \
  uint64_t _start_##NAME = __builtin_readcyclecounter()

#define ENDCOUNTER(NAME)                                 \
  uint64_t _end_##NAME = __builtin_readcyclecounter();   \
  uint64_t _cycles_##NAME = _end_##NAME - _start_##NAME

#define PRINTCPB(NAME, BYTES)                                      \
  END(NAME)                                                        \
  double _cpb_##NAME = (double)_cycles_##NAME / (double)(BYTES);   \
  fprintf(stderr, "%s: %llu cycles at %f cpb",                     \
          #NAME, _cycles_##NAME, _cpb_##NAME);

#define PRINTCYC(NAME)                                             \
  END(NAME)                                                        \
  fprintf(stderr, "%s: %llu cycles",                               \
          #NAME, _cycles_##NAME, _cpb_##NAME);


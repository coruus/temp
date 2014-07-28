clang-3.5 -fsanitize=address -g -O0 api.c salsa-vi8.c blake2/blake2b.c  -c && clang-3.5 -fsanitize=address -g -O0 api.o salsa-vi8.o blake2b.o -o test && dsymutil test && ./test

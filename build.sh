clang-3.5 -D__STDC_WANT_LIB_EXT1__=1 -std=c11 -Wextra -Wpedantic -fsanitize=address  inplace2.c api.c salsa-vi8.c blake2/blake2b.c ktutils/src/posix/mmapfile.c -I ktutils/src -O0 -g
rm test.header test.out test.tags
gtruncate -s 1M test.in

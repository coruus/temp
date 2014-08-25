yasm -f macho64 kfafx.s && clang -O3 theta.c kfafx.o -fsanitize=address && ./a.out

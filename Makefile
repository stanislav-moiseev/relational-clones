CC = gcc -O3 -g -std=c99 -pedantic -D_GNU_SOURCE	\
	-Wall -Werror -Wno-unused-function		\
	-Wno-error=maybe-uninitialized			\
	-Isrc

SRCS =			\
	src/pred.c	\
	src/clone.c	\
	src/binary.c	\
	src/z3/gen.c

OBJS =	$(SRCS:.c=.o)

.c.o:
	$(CC) -c -o $@ $^

TESTS =				\
	test/test0.out		\
	test/test-clone-read.out	\
	test/test-gen-assert-discr-fun.out

tests:  $(TESTS)

test/test0.out: test/test0.c $(OBJS)
	$(CC) -o $@ $^

test/test-clone-read.out: test/test-clone-read.c $(OBJS)
	$(CC) -o $@ $^

test/test-gen-assert-discr-fun.out: test/test-gen-assert-discr-fun.c $(OBJS)
	$(CC) -o $@ $^




clean:
	rm -f $(TESTS) $(OBJS)
	find * -name \*~ -delete


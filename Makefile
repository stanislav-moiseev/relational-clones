CC = gcc -O3 -g -std=c99 -pedantic -D_GNU_SOURCE	\
	-Wall -Werror -Wno-unused-function		\
	-Wno-error=maybe-uninitialized			\
	-Isrc

SRCS =				\
	src/pred.c		\
	src/clone.c		\
	src/clone-iterator.c	\
	src/class.c		\
	src/lattice.c		\
	src/binary.c		\
	src/z3/gen.c

OBJS =	$(SRCS:.c=.o)

.c.o:
	$(CC) -c -o $@ $^

TESTS =						\
	test/test0.out				\
	test/test-class-read.out		\
	test/test-gen-assert-discr-fun.out	\
	test/test-find-classes-with-one-subclass.out

tests:  $(TESTS)
	@./test/test0.out
	@./test/test-class-read.out
	@./test/test-gen-assert-discr-fun.out
	@./test/test-find-classes-with-one-subclass.out


test/test0.out: test/test0.c $(OBJS)
	$(CC) -o $@ $^

test/test-class-read.out: test/test-class-read.c $(OBJS)
	$(CC) -o $@ $^

test/test-gen-assert-discr-fun.out: test/test-gen-assert-discr-fun.c $(OBJS)
	$(CC) -o $@ $^

test/test-find-classes-with-one-subclass.out: test/test-find-classes-with-one-subclass.c $(OBJS)
	$(CC) -o $@ $^


clean:
	rm -f $(TESTS) $(OBJS)
	find * -name \*~ -delete


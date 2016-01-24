CC = gcc -O3 -g -std=c99 -pedantic -D_GNU_SOURCE	\
	-Wall -Werror -Wno-unused-function		\
	-Wno-error=maybe-uninitialized			\
	-Isrc -I/usr/local/inlcude			\
	-lz3

SRCS =				\
	src/pred.c		\
	src/fun.c		\
	src/clone.c		\
	src/clone-iterator.c	\
	src/class.c		\
	src/lattice.c		\
	src/algorithms.c	\
	src/binary-2013.c	\
	src/binary-2016.c	\
	src/z3/wrapper.c	\
	src/z3/gen-spec.c	\
#	src/z3/gen-text.c	\

OBJS =	$(SRCS:.c=.o)

.c.o:
	$(CC) -c -o $@ $^

TESTS =						\
	test/test0.out				\
	test/test-discr-fun-two-layers.out	\
	test/test-classes-with-one-subclass.out	\
	#test/test-high-arity.c

TESTS-2013 =					\
	test/binary/test-class-read-2013.out	\
	test/binary/test-recode-binary.out

all:  $(TESTS) $(TESTS-2013)

test: $(TESTS)
	@./test/test0.out
#	@mkdir -p output/disrc-fun-two-layers/z3
	@./test/test-discr-fun-two-layers.out
#	@mkdir -p output/classes-with-one-subclass/z3
#	@./test/test-classes-with-one-subclass.out

test/test0.out: test/test0.c $(OBJS)
	$(CC) -o $@ $^

test/z3/test-z3.out: test/z3/test-z3.c $(OBJS)
	$(CC) -o $@ $^

test/test-discr-fun-two-layers.out: test/test-discr-fun-two-layers.c $(OBJS)
	$(CC) -o $@ $^

test/test-classes-with-one-subclass.out: test/test-classes-with-one-subclass.c $(OBJS)
	$(CC) -o $@ $^


test2013:
	@./test/binary/test-class-read-2013.out

test/binary/test-class-read-2013.out: test/binary/test-class-read-2013.c $(OBJS)
	$(CC) -o $@ $^

test/binary/test-recode-binary.out: test/binary/test-recode-binary.c $(OBJS)
	$(CC) -o $@ $^


clean:
	rm -f $(TESTS) $(OBJS)
	find * -name \*~ -delete


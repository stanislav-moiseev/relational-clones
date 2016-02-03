CC = gcc -O3 -g -std=c99 -pedantic -D_GNU_SOURCE	\
	-Wall -Werror -Wno-unused-function		\
	-Wno-error=maybe-uninitialized			\
	-Isrc -I/usr/local/inlcude			\
	-lz3

SRCS =					\
	src/fun.c			\
	src/pred.c			\
	src/clone.c			\
	src/closure.c			\
					\
	src/algorithms/alg-maj.c	\
	src/algorithms/alg-closure.c	\
					\
	src/binary/maj-lattice-2013.c	\
	src/binary/common.c		\
	src/binary/maj-lattice.c	\
	src/binary/maj-classes-with-one-subclass-discr-fun.c	\
	src/binary/closure-two-preds.c	\
					\
	src/z3/z3-search.c		\
#	src/z3/gen-spec.c		\

OBJS =	$(SRCS:.c=.o)

%.o: %.c %.h
	$(CC) -c -o $@ $<

%.out: %.c $(OBJS)
	$(CC) -o $@ $^

.PRECIOUS: $(OBJS)

TESTS =						\
	test/test0.out				\
	test/test-closure.out			\
	#test/test-high-arity.c

SCRIPTS =								\
	script/binary/script-recode-binary.out				\
	script/script-maj-discr-fun-two-layers.out			\
	script/script-maj-classes-with-one-subclass.out			\
	script/script-maj-classes-with-one-subclass-discr-fun.out	\
	script/script-closure-two-preds.out				\

all:  $(TESTS) $(SCRIPTS)

test: $(TESTS)
	@./test/test0.out
	@./test/test-closure.out

clean:
	rm -f $(OBJS) $(TESTS) $(SCRIPTS)
	find * -name \*~ -delete


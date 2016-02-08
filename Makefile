CC = gcc -O3 -g -march=native						\
	-std=c99 -pedantic -D_GNU_SOURCE				\
	-Wall -Werror -Wno-unused-function				\
	-Wno-error=maybe-uninitialized					\
	-Isrc -I/usr/local/inlcude					\
	-lz3

SRCS =									\
	src/fun.c							\
	src/pred.c							\
	src/clone.c							\
	src/closure.c							\
	src/maj-lattice.c						\
	src/lattice.c							\
	src/algorithms.c						\
	src/hashtable.c							\
	src/fast-hash/fasthash.c					\
									\
	src/binary/bin-common.c						\
	src/binary/bin-maj-lattice-2013.c				\
	src/binary/bin-maj-lattice.c					\
	src/binary/bin-maj-classes-with-one-subclass-discr-fun.c	\
	src/binary/bin-closure-two-preds.c				\
									\
	src/z3/z3-search.c						\
#	src/z3/gen-spec.c						\

OBJS =	$(SRCS:.c=.o)

%.o: %.c %.h
	$(CC) -c -o $@ $<

%.out: %.c $(OBJS)
	$(CC) -o $@ $^

.PRECIOUS: $(OBJS)

TESTS =									\
	test/test0.out							\
	test/test-closure.out						\
	test/test-maj-lattice.out					\
	#test/test-high-arity.c

SCRIPTS =								\
	script/binary/script-recode-binary.out				\
	script/script-maj-discr-fun-two-layers.out			\
	script/script-maj-classes-with-one-subclass.out			\
	script/script-maj-classes-with-one-subclass-discr-fun.out	\
	script/script-closure-two-preds.out				\
	script/script-construct-lattice.out				\

all:  $(TESTS) $(SCRIPTS)

test: $(TESTS)
	@./test/test0.out
	@./test/test-closure.out

clean:
	rm -f $(OBJS) $(TESTS) $(SCRIPTS)
	find * -name \*~ -delete


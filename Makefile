CC = gcc -O3 -g -march=native						\
	-std=c99 -pedantic -D_GNU_SOURCE				\
	-Wall -Werror -Wno-unused-function				\
	-Wno-maybe-uninitialized					\
	-Isrc -I/usr/local/inlcude					\
	-lz3

SRCS =									\
	src/fun.c							\
	src/fun-majority.c						\
	src/pred.c							\
	src/pred-essential.c						\
	src/clone.c							\
									\
	src/closure.c							\
	src/closure/closure-straightforward.c				\
	src/closure/closure-two-preds.c					\
	src/closure/closure-clone-pred.c				\
	src/closure/closure2-straightforward.c				\
	src/closure/closure2-trace.c					\
	src/closure/closure2-formulas.c					\
									\
	src/maj-lattice.c						\
	src/lattice.c							\
									\
	src/hashtable.c							\
	src/fasthash/fasthash.c						\
									\
	src/binary/bin-common.c						\
	src/binary/bin-maj-lattice-2013.c				\
	src/binary/bin-maj-lattice.c					\
	src/binary/bin-maj-classes-with-one-subclass-discr-fun.c	\
	src/binary/bin-closure-two-preds.c				\
	src/binary/bin-closure-clone-pred.c				\
	src/binary/bin-lattice.c					\
	src/binary/bin-lattice-discr-fun.c				\
									\
	src/z3/z3-search.c						\
									\
	src/isar/isar-spec.c						\
									\
	script/sublattice-0-1-2-min-max/sublattice33.c			\



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
	test/test-lattice.out						\
	test/test-closure2.out						\
	#test/test-high-arity.c						\

SCRIPTS =								\
	script/binary/script-recode-binary.out				\
									\
	script/script-maj-discr-fun-two-layers.out			\
	script/script-maj-classes-with-one-subclass.out			\
	script/script-maj-classes-with-one-subclass-discr-fun.out	\
									\
	script/script-pred-equivalence-classes.out			\
	script/script-closure-two-uniq-preds.out			\
	script/script-closure-clone-pred-construct.out			\
	script/script-closure2-clone-pred-construct.out			\
									\
	script/script-lattice-construct.out				\
	script/script-lattice-discr-fun.out				\
	script/script-lattice-classes-with-discriminator.out		\
	script/script-lattice-sublattice.out				\
	script/script-lattice-statistics.out				\
									\
	script/script-isar-spec.out					\
	script/script-sublattice-0-1-2-min-max.out			\

all:  $(TESTS) $(SCRIPTS)

test: $(TESTS)
	@./test/test0.out
	@./test/test-closure.out
	@./test/test-lattice.out
	@./test/test-closure2.out

clean:
	rm -f $(OBJS) $(TESTS) $(SCRIPTS)
	find * -name \*~ -delete


## See Isabelle options in 
## ~/.isabelle/Isabelle2016/etc/settings:
ISABELLE = ~/dist/Isabelle2016/bin/isabelle

isabelle-build: script/script-isar-spec.out
	./script/script-isar-spec.out
	cp src/isar/common.thy output/R3_2
	time $(ISABELLE) build -j1 -v -b -D output/R3_2/

isabelle-jedit:
	$(ISABELLE) jedit -d output/R3_2/ -l R3_2 -n

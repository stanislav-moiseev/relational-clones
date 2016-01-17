CC = gcc -O3 -g -std=c99		\
	-Wall -Wno-unused-function	\
	-Isrc

SRCS =			\
	src/pred.c	\
	src/z3/gen.c

OBJS =	$(SRCS:.c=.o)

.c.o:
	$(CC) -c -o $@ $^


test/test0.out: test/test0.c $(OBJS)
	$(CC) -o $@ $^

TESTS =				\
	test/test0.out		\
	test/test-gen-z3.out

tests:  $(TESTS)

clean:
	rm -f $(TESTS) $(OBJS)


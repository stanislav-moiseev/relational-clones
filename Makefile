CC = gcc -O3 -g -std=c99 -Wall -Isrc

SRCS =			\
	src/pred.c	\
	src/z3/gen.c

OBJS =	$(SRCS:.c=.o)

.c.o:
	$(CC) -c -o $@ $^

.c.out:
	$(CC) $(OBJS) -o $@ $^

TESTS =				\
	test/test0.out		\
	test/test-gen-z3.out

tests:  $(OBJS) $(TESTS)

clean:
	rm -f $(TESTS) $(OBJS)


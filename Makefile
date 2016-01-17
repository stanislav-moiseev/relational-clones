CC = gcc -O3 -g -std=c99 -Wall

SRCS	= src/pred.c src/main.c

OBJS	= $(SRCS:.c=.o)

.c.o:
	$(CC) -c -o $@ $^

main.out: $(OBJS)
	$(CC) $(OBJS) -o $@

all: main.out

clean:
	rm -f main.out $(OBJS)


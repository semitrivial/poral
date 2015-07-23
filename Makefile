CC = gcc
FLAGS = -Wall -Werror -g
DEPS = core.h macro.h patterns.h por.h

all: example

example: arith.o core.o example.o patterns.o por.o simp.o
	$(CC) $(FLAGS) arith.o core.o example.o patterns.o por.o simp.o -o example

%.o: %.c $(DEPS)
	$(CC) $(FLAGS) -o $@ -c $<

clean:
	rm -f *.o


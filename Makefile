CC = gcc
CFLAGS = -O3

all:	gfind

gfind:
	$(CC) -o gfind gfind.c

clean:
	rm gfind

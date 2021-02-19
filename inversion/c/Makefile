MONTY_SRCS = $(wildcard montgomery/*_test.c) $(wildcard montgomery_jump/*_test.c) $(wildcard montgomery_jump_alt/*_test.c) 
MONTY_PROGS = $(patsubst %.c,%,$(MONTY_SRCS))

SOLINAS_SRCS = $(wildcard solinas/*_test.c) $(wildcard solinas_jump/*_test.c) $(wildcard solinas_jump_alt/*_test.c) 
SOLINAS_PROGS = $(patsubst %.c,%,$(SOLINAS_SRCS))

CC = gcc
CFLAGS = -O3 -march=native

all: $(MONTY_PROGS) $(SOLINAS_PROGS)

%: %.c
	$(CC) $(CFLAGS) -o $@ $<

clean: 
	rm -f $(MONTY_PROGS) $(SOLINAS_PROGS)

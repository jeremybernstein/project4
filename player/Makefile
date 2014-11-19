.PHONY: prof run

CXX = gcc
TARGET := leiserchess
SRC := util.c tt.c fen.c move_gen.c search.c eval.c abort.c speculative_add.c
OBJ := $(SRC:.c=.o)

ifeq ($(PARALLEL),1)
	PFLAG := -DPARALLEL -D_BSD_SOURCE # -g needed for test framework assertions
else
	PFLAG := 
endif

CFLAGS = -std=c99 -Wall -fcilkplus
ifeq ($(TEST),1)
	CFLAGS += -O0 -g -DTEST $(PFLAG) # -g needed for test framework assertions
else
	CFLAGS += -O3 -DNDEBUG $(PFLAG)
endif

ifeq ($(REFERENCE),1)
	CFLAGS += -DRUN_REFERENCE_CODE=1
endif

ifndef DEPTH
	DEPTH=8
endif

LDFLAGS= -Wall -lrt -lm -lcilkrts -ldl -lpthread

.PHONY : default clean 

default : $(TARGET)

# Each C source file will have a corresponding file of prerequisites.
# Include the prerequisites for each of our C source files.
-include $(SRC:.c=.d)

# This rule generates a file of prerequisites (i.e., a makefile)
# called name.d from a C source file called name.c.
%.d : %.c
	@set -e; rm -f $@; \
	$(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	sed 's,\($*\)\.o[ :]*,\1.o $@ : ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$

%.o : %.c
	$(CXX) $(CFLAGS) $(LDFLAGS) -c $< -o $@

search.c: search_ref.c search_mod.c


leiserchess : leiserchess.o $(OBJ)
	$(CXX) $^ $(LDFLAGS) -o $@

clean :
	rm -f *.o *.d* *~ $(TARGET)

prof: clean leiserchess
	echo "go depth $(DEPTH) quit" | perf record ./leiserchess && perf report

run: leiserchess
	echo "go depth $(DEPTH) quit" | ./leiserchess >> .output && python parse_score.py

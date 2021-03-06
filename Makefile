
# SDD Directory 
SDD	= sdd-1.1.1/

# ---- COMPILERS ----
# C++ compiler
CPP     = g++
# C compiler
CC 	= gcc

# CPP compilation flags
CPPFLAGS = -O3 -W -g -finline-functions -Llib -lsdd -lm 
INCLUDE = -Iinclude

# ---- END COMPILERS ----

GCC_MAJOR := $(shell (echo|gcc -dM -E -|grep __GNUC__|cut -d' ' -f3))
GCC_MINOR := $(shell (echo|gcc -dM -E -|grep __GNUC_MINOR__|cut -d' ' -f3))
GCC_PATCHLEVEL := $(shell (echo|gcc -dM -E -|grep __GNUC_PATCHLEVEL__|cut -d' ' -f3))

GRAMMAR		= parser/nssis
LEXFILE 	= parser/nssis
DRIVER		= parser/mcmas-driver
SYNTAXCHECK	= parser/syntaxcheck
UTILITIES	= utilities/utilities
READ_OPTIONS = utilities/read_options
ATOMIC_PROPOSITION = utilities/atomic_proposition
ARITHMETIC_EXPRESSION = utilities/arithmetic_expression
ASSIGNMENT = utilities/assignment
BASIC_AGENT = utilities/basic_agent
BASICTYPE = utilities/basictype
BIT_EXPRESSION = utilities/bit_expression
BOOL_EXPRESSION = utilities/bool_expression
BOOL_VALUE = utilities/bool_value
ENUMERATE = utilities/enumerate
ENUM_VALUE = utilities/enum_value
EVOLUTION_LINE = utilities/evolution_line
EXPRESSION = utilities/expression
FAIRNESS_EXPRESSION = utilities/fairness_expression
INT_VALUE = utilities/int_value
LACTION = utilities/laction
LOGIC_EXPRESSION = utilities/logic_expression
MODAL_FORMULA = utilities/modal_formula
OBJECT = utilities/object
PROTOCOL_LINE = utilities/protocol_line
RANGEDINT = utilities/rangedint
VARIABLE = utilities/variable
MAIN		= main_sdd
LEX		= flex
YACC		= bison


############################################################################
# Find which version of Bison is used
BISON_VERSION := $(shell (echo|$(YACC) --version|grep bison|cut -d' ' -f4))
ifeq ($(BISON_VERSION), 2.3)
	BISONSUFFIX =
else
	BISONSUFFIX = _new
endif
############################################################################

SDDLIB = lib/libsdd.a
SDD_MAKEFILE = Makefile

PTHREADLIB = -lpthread

default: all

all: mcmas  

makesdd: 
	cd $(SDD) && make

OBJECTS = parser/lex.yy.o $(GRAMMAR).o $(READ_OPTIONS).o $(DRIVER).o $(SYNTAXCHECK).o $(UTILITIES).o $(ATOMIC_PROPOSITION).o $(BASIC_AGENT).o $(BASICTYPE).o $(BIT_EXPRESSION).o $(BOOL_EXPRESSION).o $(BOOL_VALUE).o $(ENUMERATE).o $(ENUM_VALUE).o $(EVOLUTION_LINE).o $(EXPRESSION).o $(FAIRNESS_EXPRESSION).o $(ARITHMETIC_EXPRESSION).o $(ASSIGNMENT).o $(INT_VALUE).o $(LACTION).o $(LOGIC_EXPRESSION).o $(MODAL_FORMULA).o $(OBJECT).o $(PROTOCOL_LINE).o $(RANGEDINT).o $(VARIABLE).o

mcmas : $(OBJECTS) $(MAIN).cc $(SDDLIB)
	$(CPP) $(CPPFLAGS) $(INCLUDE) $(SDDLIB) $(PTHREADLIB) $(OBJECTS) -o mcmas $(MAIN).cc $(SDDLIB)

parser/lex.yy.o: $(LEXFILE).ll $(GRAMMAR)$(BISONSUFFIX).yy
	$(LEX) -oparser/lex.yy.c $(LEXFILE).ll

	$(YACC) --defines=$(GRAMMAR).hh $(GRAMMAR)$(BISONSUFFIX).yy -o $(GRAMMAR).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE)  -c parser/lex.yy.c -o parser/lex.yy.o

$(GRAMMAR).o: include/utilities.hh include/types.hh $(LEXFILE).ll $(GRAMMAR)$(BISONSUFFIX).yy
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(GRAMMAR).cc -o $(GRAMMAR).o

$(SYNTAXCHECK).o: include/utilities.hh include/types.hh $(SYNTAXCHECK).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(SYNTAXCHECK).cc -o $(SYNTAXCHECK).o

$(UTILITIES).o: include/utilities.hh $(UTILITIES).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(UTILITIES).cc -o $(UTILITIES).o

$(READ_OPTIONS).o: include/utilities.hh $(READ_OPTIONS).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(READ_OPTIONS).cc -o $(READ_OPTIONS).o

$(ATOMIC_PROPOSITION).o: include/utilities.hh include/types.hh $(ATOMIC_PROPOSITION).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(ATOMIC_PROPOSITION).cc -o $(ATOMIC_PROPOSITION).o

$(ARITHMETIC_EXPRESSION).o: include/utilities.hh include/types.hh $(ARITHMETIC_EXPRESSION).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(ARITHMETIC_EXPRESSION).cc -o $(ARITHMETIC_EXPRESSION).o

$(ASSIGNMENT).o: include/utilities.hh include/types.hh $(ASSIGNMENT).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(ASSIGNMENT).cc -o $(ASSIGNMENT).o

$(BASIC_AGENT).o: include/utilities.hh include/types.hh $(BASIC_AGENT).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(BASIC_AGENT).cc -o $(BASIC_AGENT).o

$(BASICTYPE).o: include/utilities.hh include/types.hh $(BASICTYPE).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(BASICTYPE).cc -o $(BASICTYPE).o

$(BIT_EXPRESSION).o: include/utilities.hh include/types.hh $(BIT_EXPRESSION).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(BIT_EXPRESSION).cc -o $(BIT_EXPRESSION).o

$(BOOL_EXPRESSION).o: include/utilities.hh include/types.hh $(BOOL_EXPRESSION).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(BOOL_EXPRESSION).cc -o $(BOOL_EXPRESSION).o

$(BOOL_VALUE).o: include/utilities.hh include/types.hh $(BOOL_VALUE).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(BOOL_VALUE).cc -o $(BOOL_VALUE).o


$(ENUMERATE).o: include/utilities.hh include/types.hh $(ENUMERATE).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(ENUMERATE).cc -o $(ENUMERATE).o

$(ENUM_VALUE).o: include/utilities.hh include/types.hh $(ENUM_VALUE).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(ENUM_VALUE).cc -o $(ENUM_VALUE).o

$(EVOLUTION_LINE).o: include/utilities.hh include/types.hh $(EVOLUTION_LINE).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(EVOLUTION_LINE).cc -o $(EVOLUTION_LINE).o

$(EXPRESSION).o: include/utilities.hh include/types.hh $(EXPRESSION).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(EXPRESSION).cc -o $(EXPRESSION).o

$(FAIRNESS_EXPRESSION).o: include/utilities.hh include/types.hh $(FAIRNESS_EXPRESSION).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(FAIRNESS_EXPRESSION).cc -o $(FAIRNESS_EXPRESSION).o

$(INT_VALUE).o: include/utilities.hh include/types.hh $(INT_VALUE).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(INT_VALUE).cc -o $(INT_VALUE).o

$(LACTION).o: include/utilities.hh include/types.hh $(LACTION).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(LACTION).cc -o $(LACTION).o

$(LOGIC_EXPRESSION).o: include/utilities.hh include/types.hh $(LOGIC_EXPRESSION).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(LOGIC_EXPRESSION).cc -o $(LOGIC_EXPRESSION).o

$(MODAL_FORMULA).o: include/utilities.hh include/types.hh $(MODAL_FORMULA).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(MODAL_FORMULA).cc -o $(MODAL_FORMULA).o

$(OBJECT).o: include/utilities.hh include/types.hh $(OBJECT).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(OBJECT).cc -o $(OBJECT).o

$(PROTOCOL_LINE).o: include/utilities.hh include/types.hh $(PROTOCOL_LINE).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(PROTOCOL_LINE).cc -o $(PROTOCOL_LINE).o

$(RANGEDINT).o: include/utilities.hh include/types.hh $(RANGEDINT).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(RANGEDINT).cc -o $(RANGEDINT).o

$(VARIABLE).o: include/utilities.hh include/types.hh $(VARIABLE).cc
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(VARIABLE).cc -o $(VARIABLE).o

$(DRIVER).o: $(DRIVER).cc 
	$(CPP) $(CPPFLAGS) $(INCLUDE) -c $(DRIVER).cc -o $(DRIVER).o 

.PHONY : clean
clean: cleanmcmas

cleanmcmas:
	rm $(MCMASEXE) $(OBJECTS) parser/lex.yy.c parser/location.hh parser/position.hh parser/stack.hh $(GRAMMAR).hh $(GRAMMAR).cc 

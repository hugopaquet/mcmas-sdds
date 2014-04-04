#
# This file is part of Boolean Expression Solver. Boolean Expression Solver is
# a program to build a truth table for a Boolean expression.
# 
# Copyright (C) 2007 Chris Bouchard
# 
# Boolean Expression Solver is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or (at your
# option) any later version.
# 
# Boolean Expression Solver is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General
# Public License for more details.
# 
# You should have received a copy of the GNU General Public License along with
# Boolean Expression Solver; if not, write to the Free Software Foundation,
# Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
#


BIN_DIR := bin
SRC_DIR := src
SHELL_SCRIPT := boolsolve

SOURCE_EXT := .java
OBJECT_EXT := .class

PACKAGES := net/jbouchard/bool
MAIN_CLASS := net.jbouchard.bool.BooleanExpressionSolver

JAVAFLAGS :=

DEPENDENCIES := $(foreach package,$(PACKAGES),$(foreach file,$(wildcard $(SRC_DIR)/$(package)/*$(SOURCE_EXT)),$(package)/$(basename $(notdir $(file)))))

.PHONY : clean
.PHONY : javadoc
.PHONY : cleandoc

all : BooleanExpressionSolver $(SHELL_SCRIPT)

BooleanExpressionSolver : $(BIN_DIR) $(foreach dependency,$(DEPENDENCIES),$(BIN_DIR)/$(dependency)$(OBJECT_EXT))

$(BIN_DIR)/%.class : $(SRC_DIR)/%$(SOURCE_EXT)
	javac -sourcepath $(SRC_DIR) $< -d $(BIN_DIR) $(JAVAFLAGS)

$(BIN_DIR) :
	mkdir $(BIN_DIR)

$(SHELL_SCRIPT) :
	echo "java -cp $(BIN_DIR) $(MAIN_CLASS) \$$@" > $(SHELL_SCRIPT)
	chmod u+x $(SHELL_SCRIPT)

clean :
	rm -rf $(BIN_DIR)
	rm -f $(SHELL_SCRIPT)

javadoc :
	ant -f javadoc.xml

cleandoc :
	rm -rf doc

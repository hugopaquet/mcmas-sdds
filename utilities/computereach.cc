#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <string>
#include <iostream>
#include <fstream>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <cctype>
#include <ctime>
#include "types.hh"
#include "utilities.hh"
extern "C" {
	#include "sddapi.h"
}

// #define num_of_threads1 2
// #define num_of_blocks 2
// #define time_of_iteration 5


extern void *compute_reach_parallel( void *ptr );


SddNode* compute_reach(SddNode* in_st, SddManager* manager, struct parameters * params, SddNode* full_transition_relation,
                  unsigned int *acounter1, int id, unsigned long *threadmem) {
  

	SddNode* reach = sdd_manager_false(manager);

  SddNode* q1 = in_st;
  SddNode* next1 = sdd_manager_false(manager);

/* Algo:    
Y = false;	
X = in_st;
while(q1 != Y)
{
	Y = q1
	next1 = Exists(all non-primed variables, conjoin(X, transition_relation))
	unprime next1
	q1 = disjoin(q1, next1)
}

return q1

*/

while (!sdd_node_is_true(sdd_equiv(q1, reach, manager))) {
      
      reach = q1;
      next1 = q1;
			next1 = conjoin(next1, full_transition_relation, manager);
			for(unsigned int i = 0; i < params->variable_sdds->size(); i++) {
				SddLiteral* literal = sdd_node_literal((*params->variable_sdds)[i]);
				next1 = sdd_exists(literal, next1, manager);
			} 
			// un-prime variables
			SddLiteral* map = new SddLiteral[33]; 
			for(int i = 1; i < )
			next1 = sdd_rename_variables(next1, map, manager);
   //   next1 = next1.SwapVariables(*v, *pv);
     // next1 = Exists(bddmgr, a, next1); // Clear actions.
      
   //   q1 = q1 + next1;
    //  (*acounter1)++;
  }

  return reach;
}


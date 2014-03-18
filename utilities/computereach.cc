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

 /* while (!sdd_node_is_true(sdd_equiv(q1, reach, manager))) {
      
      reach = q1;
      next1 = q1;
			next1 = conjoin(next1, full_transition_relation, manager);

      next1 = Exists(bddmgr, v, next1);
      next1 = next1.SwapVariables(*v, *pv);
      next1 = Exists(bddmgr, a, next1); // Clear actions.
      
      q1 = q1 + next1;
      (*acounter1)++;
  }
*/
  return reach;
}


#define URL "http://vas.doc.ic.ac.uk/tools/mcmas/"

#include <unistd.h>
//#include <sys/syscall.h>
#include <sys/types.h>
#include <sched.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <signal.h>
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
#include "mcmas-driver.hh"
#include <sys/timeb.h>

extern "C" {
	#include "sddapi.h"
}
using namespace std;

vector< string * >*string_table;
vector< bool_expression * >*logic_expression_table;
vector< bool_expression * >*logic_expression_table1;
vector< variable * >*variable_table;
map< string, basic_agent * >*is_agents;
vector< basic_agent * >*agents;
map< string, bool_expression * >*is_evaluation;
bool_expression *is_istates = NULL;
map< string, set< string > >*is_groups;
vector< modal_formula > *is_formulae;
vector< fairness_expression * >*is_fairness;
int obsvars_bdd_length;
int envars_bdd_length;
// A map to store global options, e.g. verbosity, etc.
map< string, int >options;
string cex_prefix;    // Destination directory for counterexamples
int scount;     // a global counter for counterexamples.
int states_count = 0;
int actions_count = 0;
//bdd_parameters * parameters; /* copy of the single parameters for the signal handler */

bool global_consistency_check();
bool read_options(int argc, char *argv[]);
void print_help(void);

void
mcmas_signal_handler(int signal)
{
  /* using cerr here seems to disagree with Linux */

  fprintf(stderr, "\nCaught signal ");
  switch (signal)	{
	case SIGINT:
    fprintf(stderr, "SIGINT\n");
    break;
  case SIGPIPE:
    fprintf(stderr, "SIGPIPE\n");
    break;
  case SIGABRT:
    fprintf(stderr, "SIGABRT\n");
    break;
  case SIGTERM:
    fprintf(stderr, "SIGTERM\n");
    break;
  default:
    fprintf(stderr, "SIG OTHER\n");
    break;
  }

  /* check if we have bdd_stats */
/*  if (options["bdd_stats"] == 1) {
    // check if we have a single BDD parameter and a bddmgr 
    if (parameters && (parameters->bddmgr))	{
      parameters->bddmgr->info(); // print the current bdd stats 
    }
  } */
  exit(signal);
}

void
print_banner(void)
{
  cout <<
    "************************************************************************"
       << endl;
  cout << "A Model Checker Based on Multi-Agent Systems" << endl;
  cout << "\t\tThis version uses SDDs." << endl;
  cout <<
    "************************************************************************"
       << endl << endl;
}

/*
void
print_state(BDD state, vector<BDD> v)
{
  for (unsigned int i = 0; i < agents->size(); i++) {
    cout << "Agent " << (*agents)[i]->get_name() << endl;
    (*agents)[i]->print_state("  ", state, v);
  }
}

string
state_to_str(BDD state, vector<BDD> v)
{
  ostringstream s;

  for (unsigned int i = 0; i < agents->size(); i++) {
    s << "  Agent " << (*agents)[i]->get_name() << "\n";
    s << (*agents)[i]->state_to_str(state, v);

  }
  return s.str();
}
*/
bool
find_same_state(map< string, int >*statehash, string state)
{
  if (statehash != NULL) {
    map< string, int >::iterator iter = statehash->find(state);
    if (iter != statehash->end()) {
      return true;
    }
  }
  return false;
}
/*
bool
is_valid_state(BDD state, vector<BDD> v)
{
  for (unsigned int i = 0; i < agents->size(); i++) {
    if (!(*agents)[i]->is_valid_state(state, v))
      return false;
  }
  return true;
}

void
print_action(BDD state, vector<BDD> a)
{
  for (unsigned int i = 0; i < agents->size(); i++) {
    cout << (*agents)[i]->get_name() << " : ";
    (*agents)[i]->print_action(state, a);
    if (i < agents->size() - 1)
      cout << "; ";
    else
      cout << endl;
  }
}

void
print_action_1(BDD state, vector<BDD> a)
{
  for (unsigned int i = 0; i < agents->size(); i++) {
    cout << (*agents)[i]->get_name() << " : ";
    (*agents)[i]->print_action(state, a);
    cout << "; ";
  }
  cout << endl;
}

bool
is_valid_action(BDD state, vector<BDD> a)
{
  for (unsigned int i = 0; i < agents->size(); i++) {
    if (!(*agents)[i]->is_valid_action(state, a))
      return false;
  }
  return true;
}

BDD
append_variable_BDDs(Cudd * bddmgr, vector<BDD> * v, BDD a)
{
  for (unsigned int j = 0; j < agents->size(); j++) {
    map< string, basictype * >*obsvars = (*agents)[j]->get_obsvars();
    if (
vars != NULL && obsvars->size() > 0)
      for (map< string, basictype * >::iterator i =
             obsvars->begin(); i != obsvars->end(); i++)
        if ((*i).second->get_type() == 3)
          a *= ((enumerate *) (*i).second)->build_all_BDDs(bddmgr, v);
    map< string, basictype * >*vars = (*agents)[j]->get_vars();
    if (vars != NULL && vars->size() > 0)
      for (map< string, basictype * >::iterator i = vars->begin();
           i != vars->end(); i++)
        if ((*i).second->get_type() == 3)
          a *= ((enumerate *) (*i).second)->build_all_BDDs(bddmgr, v);
  }
  return a;
}

BDD
append_variable_BDD(Cudd * bddmgr, vector<BDD> * v, BDD a, int j)
{
  map< string, basictype * >*obsvars = (*agents)[j]->get_obsvars();
  if (obsvars != NULL && obsvars->size() > 0)
    for (map< string, basictype * >::iterator i = obsvars->begin();
         i != obsvars->end(); i++)
      if ((*i).second->get_type() == 3)
        a *= ((enumerate *) (*i).second)->build_all_BDDs(bddmgr, v);
  map< string, basictype * >*vars = (*agents)[j]->get_vars();
  if (vars != NULL && vars->size() > 0)
    for (map< string, basictype * >::iterator i = vars->begin();
         i != vars->end(); i++)
      if ((*i).second->get_type() == 3)
        a *= ((enumerate *) (*i).second)->build_all_BDDs(bddmgr, v);
  return a;
}

void free_mcmas_memory(bdd_parameters *para) {
  for(unsigned int i=0; i<agents->size(); i++)
    delete (*agents)[i];
  delete agents;
  delete is_agents;
  for(map<string, bool_expression *>::iterator it = is_evaluation->begin(); it != is_evaluation->end(); it++) {
    if((it->first).compare("_init") != 0 || it->second->get_op() != 0)
      delete it->second;
  }
  delete is_evaluation;
  delete is_groups;
  delete is_formulae;
  for(unsigned int i=0; i<is_fairness->size(); i++) {
    (*is_fairness)[i]->delete_bdd_representation(para);
    delete (*is_fairness)[i];
  }
  delete is_fairness;
  for(unsigned int i=0; i<logic_expression_table->size(); i++) {
    logic_expression *tmp = (logic_expression *)((*logic_expression_table)[i]->get_operand(0));
    delete (*logic_expression_table)[i];
    delete tmp;
  }
  delete logic_expression_table;
  for(unsigned int i=0; i<logic_expression_table1->size(); i++) {
    logic_expression *tmp = (logic_expression *)((*logic_expression_table1)[i]->get_operand(0));
    delete (*logic_expression_table1)[i];
    delete tmp;
  }
  delete logic_expression_table1;
  for(unsigned int i=0; i<string_table->size(); i++) {
    delete (*string_table)[i];
  }
  delete string_table;
  for(unsigned int i=0; i<variable_table->size(); i++)
    delete (*variable_table)[i];
  delete variable_table;
}


*/

SddNode* 
compute_reach(SddNode* in_st, SddManager* manager, struct parameters * params, vector<SddNode*>* transition_relation_sdds) {
 

	SddNode* tmp;
	SddNode* rt = sdd_manager_true(manager);

  SddNode* reach = in_st;
  SddNode* next1 = in_st;
  
	unsigned int v = params->variable_sdds->size(); // number of state variables
	unsigned int a = params->action_variable_sdds->size(); // number of action variables
	SddLiteral map[2 * v + a + 1]; 
  for(unsigned int i = 1; i <= v; i++) {	
		map[i] = sdd_node_literal((*params->variable_sdds)[i-1]); 
	}
	for(unsigned int i = v + 1; i <= 2 * v; i++) {
		map[i] = sdd_node_literal((*params->variable_sdds)[i - v - 1]); 
	}
	for(unsigned int i = 2 * v + 1; i <= 2 * v + a; i++) {
		map[i] = sdd_node_literal((*params->action_variable_sdds)[i - 2 * v - 1]); 
	}
  while (true) {
      struct timeb tmb;
    ftime(&tmb);
     cout << "iter" << endl;
     cout << "\tA";
     struct timeb tmb2;
    ftime(&tmb2);
     	  if(options["dao"])
		  sdd_manager_auto_gc_and_minimize_off(manager);
    for(unsigned int i = 0; i < agents->size(); i++) {
         cout << ".";
         cout.flush();
      next1 = sdd_conjoin((*transition_relation_sdds)[i], next1, manager);
	    sdd_ref(next1, manager);
			//sdd_deref(tmp, manager);
	  }
	   	  if(options["dao"])
		  sdd_manager_auto_gc_and_minimize_on(manager);
	  struct timeb tmb3;
    ftime(&tmb3);
    cout << "  (" << ((tmb3.time-tmb2.time) + (tmb3.millitm-tmb2.millitm)/1000.0) << ")" << endl;
	  cout << "\tB";
	   ftime(&tmb2);
 	  if(options["dao"])
		  sdd_manager_auto_gc_and_minimize_off(manager);
		for(unsigned int i = 0; i < v; i++) {
		  cout << ".";
		  cout.flush();
			next1 = sdd_exists(sdd_node_literal((*params->variable_sdds)[i]), tmp = next1, manager);
			sdd_ref(next1, manager);
			sdd_deref(tmp, manager);
		} 
		    ftime(&tmb3);
    cout << "  (" << ((tmb3.time-tmb2.time) + (tmb3.millitm-tmb2.millitm)/1000.0) << ")" << endl;
		if(options["dao"])
			sdd_manager_auto_gc_and_minimize_on(manager);
    cout << "\tC";
    cout.flush();
    	   ftime(&tmb2);
		next1 = sdd_rename_variables(tmp = next1, map, manager);
		sdd_ref(next1, manager);
		sdd_deref(tmp, manager);
		if(options["dao"])
	  	sdd_manager_auto_gc_and_minimize_off(manager);
	  	    ftime(&tmb3);
    cout << "  (" << ((tmb3.time-tmb2.time) + (tmb3.millitm-tmb2.millitm)/1000.0) << ")" << endl;
	  cout << "\tD";
	  	   ftime(&tmb2);
		for(unsigned int i = 0; i < a; i++) {
			cout << ".";
			cout.flush();
			next1 = sdd_exists(sdd_node_literal((*params->action_variable_sdds)[i]), tmp = next1, manager);
			sdd_ref(next1, manager);
			sdd_deref(tmp, manager);
		}	  	    
		ftime(&tmb3);
    cout << "  (" << ((tmb3.time-tmb2.time) + (tmb3.millitm-tmb2.millitm)/1000.0) << ")" << endl;

    cout << "\tE" ;
    cout.flush();
    	   ftime(&tmb2);
		next1 = sdd_conjoin(tmp = next1, sdd_negate(reach, manager), manager);
		sdd_ref(next1, manager);
		sdd_deref(tmp, manager);

    if (sdd_node_is_false(next1))
      break;
    else {
		  reach = sdd_disjoin(tmp = reach, next1, manager);
			sdd_ref(reach, manager);
			sdd_deref(tmp, manager);

		}
		if(options["dao"])
	  	sdd_manager_auto_gc_and_minimize_on(manager); 
				ftime(&tmb3);
    cout << "  (" << ((tmb3.time-tmb2.time) + (tmb3.millitm-tmb2.millitm)/1000.0) << ")" << endl;
		sdd_manager_garbage_collect(manager);
		struct timeb tmb1;
    ftime(&tmb1);
    cout << "\t iteration time = " << ((tmb1.time-tmb.time) + (tmb1.millitm-tmb.millitm)/1000.0) << endl;
  }	
    
  return reach;
}


vector<SddNode*>* 
compute_action_variable_sdds(SddManager* manager)
{
	vector<SddNode*>* a = new vector<SddNode*>;
//	if(options["ordering"] == 1) {
		for(int i = 1; i <= actions_count; i++) {
			a->push_back(sdd_manager_literal(states_count*2 + i, manager));			
		}
		return a;	
//	}
//	if(options["ordering"] == 2) {
//
//	}
}


vector<SddNode*>* 
compute_variable_sdds(SddManager* manager)
{
	vector<SddNode*>* v = new vector<SddNode*>;
	for(int i = 1; i <= states_count; i++) {
		v->push_back(sdd_manager_literal(i, manager));
	} 
	

	return v;
}

vector<SddNode*>*
compute_primed_variable_sdds(SddManager* manager) 
{
	vector<SddNode*>* pv = new vector<SddNode*>;
	for(int i = 1; i <= states_count; i++) { 
		pv->push_back(sdd_manager_literal(states_count + i, manager));
	}
	return pv;
}

void 
print_params(struct parameters * params) 
{
	cout << "Params:" << endl;
	cout << "No. of state variables: " << states_count << endl;
	cout << "No. of action variables: " << actions_count << endl;
	cout << "Action vector: " << "Size " << params->action_variable_sdds->size() << endl;
	for(unsigned int i = 0; i < params->action_variable_sdds->size(); i++) {
		if((*params->action_variable_sdds)[i] == 0)
			cout << "	null for i = " << i << endl; 
	}
	cout << "Variable vector: " << "Size " << params->variable_sdds->size() << endl;	
	for(unsigned int i = 0; i < params->variable_sdds->size(); i++) 
		if((*params->variable_sdds)[i] == 0)
			cout << "		null for i = " << i << endl; 
	cout << "Primed variable vector: " << "Size " << params->primed_variable_sdds->size() << endl;
	for(unsigned int i = 0; i < params->primed_variable_sdds->size(); i++) 
		if((*params->primed_variable_sdds)[i] == 0)
			cout << "		null for i = " << i << endl; 

}

SddLiteral* 
get_var_order(int ordering_type, vector< basic_agent * >* agents) 
{
	int var_count = 2 * states_count + actions_count;
	SddLiteral* var_order = new SddLiteral[var_count];
	switch(ordering_type) {
	case 1: 
	{
		for(int i = 1; i <= var_count; i++)
			var_order[i-1] = i;
		break;
	}
	case 2:
	{
		int tmp_sum = 0;
		int tmp_var = 0;
		int tmp_acts = 0;
		for (unsigned int i = 0; i < agents->size(); i++) {
			for(int j = tmp_var; j < tmp_var + (*agents)[i]->state_BDD_length(); j++) {
				var_order[tmp_sum + 2 * (j - tmp_var) ] = j + 1;
				var_order[tmp_sum + 2 * (j - tmp_var) + 1] = states_count + j + 1; 
			}
			tmp_var += (*agents)[i]->state_BDD_length();
			tmp_sum += (*agents)[i]->state_BDD_length() * 2;
			for(unsigned int j = tmp_acts; j < tmp_acts + (*agents)[i]->actions_BDD_length(); j++) {
				var_order[tmp_sum + j - tmp_acts] = 2 * states_count + j + 1;
			}
			tmp_acts += (*agents)[i]->actions_BDD_length();
			tmp_sum += (*agents)[i]->actions_BDD_length();
		}
		break;
	}
	case 3: 
	{
		int tmp_sum = 0;
		int tmp_var = 0;
		int tmp_acts = 0;
		for (unsigned int i = 0; i < agents->size(); i++) {
			for(int j = tmp_var; j < tmp_var + (*agents)[i]->state_BDD_length(); j++) {
				var_order[tmp_sum + (j - tmp_var)] = j + 1;
			}
			tmp_sum += (*agents)[i]->state_BDD_length();
			for(unsigned int j = tmp_acts; j < tmp_acts + (*agents)[i]->actions_BDD_length(); j++) {
				var_order[tmp_sum + j - tmp_acts] = 2 * states_count + j + 1;
			}
			tmp_acts += (*agents)[i]->actions_BDD_length();
			tmp_sum += (*agents)[i]->actions_BDD_length();
			for(int j = tmp_var; j < tmp_var + (*agents)[i]->state_BDD_length(); j++) {
				var_order[tmp_sum + (j - tmp_var)] = states_count + j + 1; 
			}	
			tmp_var += (*agents)[i]->state_BDD_length();
			tmp_sum += (*agents)[i]->state_BDD_length();
		}
		break;
	}
	case 4: 
	{
		int tmp_sum = 0;
		int tmp_var = 0;
		int tmp_acts = 0;
		for (unsigned int i = 0; i < agents->size(); i++) {
			for(int j = tmp_var; j < tmp_var + (*agents)[i]->state_BDD_length(); j++) {
				var_order[tmp_sum + (j - tmp_var)] = j + 1;
			}
			tmp_sum += (*agents)[i]->state_BDD_length();
			for(int j = tmp_var; j < tmp_var + (*agents)[i]->state_BDD_length(); j++) {
				var_order[tmp_sum + (j - tmp_var)] = states_count + j + 1; 
			}	
			tmp_var += (*agents)[i]->state_BDD_length();
			tmp_sum += (*agents)[i]->state_BDD_length();
			for(unsigned int j = tmp_acts; j < tmp_acts + (*agents)[i]->actions_BDD_length(); j++) {
				var_order[tmp_sum + j - tmp_acts] = 2 * states_count + j + 1;
			}
			tmp_acts += (*agents)[i]->actions_BDD_length();
			tmp_sum += (*agents)[i]->actions_BDD_length();
		}
    break;	
	}	
	case 5:
	{
	  int tmp_sum = 0;
		int tmp_var = 0;
		int tmp_acts = 0;
		for (unsigned int i = 0; i < agents->size(); i++) {
			for(int j = tmp_var; j < tmp_var + (*agents)[i]->state_BDD_length(); j++) {
				var_order[tmp_sum + (j - tmp_var)] = j + 1;
			}
			tmp_sum += (*agents)[i]->state_BDD_length();
			for(int j = tmp_var; j < tmp_var + (*agents)[i]->state_BDD_length(); j++) {
				var_order[tmp_sum + (j - tmp_var)] = states_count + j + 1; 
			}	
			tmp_var += (*agents)[i]->state_BDD_length();
			tmp_sum += (*agents)[i]->state_BDD_length();
			for(unsigned int j = tmp_acts; j < tmp_acts + (*agents)[i]->actions_BDD_length(); j++) {
				var_order[tmp_sum + j - tmp_acts] = 2 * states_count + j + 1;
			}
			tmp_acts += (*agents)[i]->actions_BDD_length();
			tmp_sum += (*agents)[i]->actions_BDD_length();
		}	
		
	  break;
	
	}
	default:
		cout << "There is no ordering of type " << ordering_type << endl;
		exit(0);
	}

	return var_order;

}


int
main(int argc, char *argv[])
{
	
  struct timeb tmb;
  ftime(&tmb);

  struct sigaction sigact;
  sigact.sa_handler = mcmas_signal_handler;
  sigemptyset(&sigact.sa_mask);
  sigact.sa_flags = 0;

  /* signals we want to catch */
  sigaction(SIGINT, &sigact, 0); /* interrupt */
  sigaction(SIGPIPE, &sigact, 0); /* broken pipe, used for timeouts */
  sigaction(SIGABRT, &sigact, 0); /* abort */
  sigaction(SIGTERM, &sigact, 0); /* term, debatable if we can actually catch this */

  unsigned long threadmem = 0;
  std::string filename;
  string s;
  mcmas_driver driver;

  if (argc < 2) {
    print_banner();
    print_help();
    exit(1);
  }

  cex_prefix = "";

  if (read_options(argc, argv))
    exit(1);

  print_banner();

	SddNode* tmp; 
  is_agents = new map< string, basic_agent * >;
  agents = new vector< basic_agent * >;
  is_evaluation = new map< string, bool_expression * >;
  is_groups = new map< string, set< string > >;
  is_formulae = new vector< modal_formula >;
  is_fairness = new vector< fairness_expression * >;

  string_table = new vector< string * >;
  string_table->push_back(new string("Environment"));
  logic_expression_table = new vector< bool_expression * >;
  logic_expression_table1 = new vector< bool_expression * >;
  variable_table = new vector< variable * >;

  filename = argv[argc - 1];
  driver.parse(filename);
  if (!driver.syntax_error) {
     cout << filename << " has been parsed successfully." << endl;
     cout << "Global syntax checking..." << endl;
    if (!global_consistency_check()) {
      cout << filename << " has error(s)." << endl;
      //free_mcmas_memory(NULL);
      exit(-1);
    }
    if (options["quiet"] == 0)
      cout << "Done" << endl;
  } else {
    cout << filename << " has syntax error(s)." << endl;
   // free_mcmas_memory(NULL);
    exit(-1);
  }


	// Count number of boolean variables needed to encode the model (states and actions)
	for (unsigned int i = 0; i < agents->size(); i++) {
 	  states_count += (*agents)[i]->state_BDD_length();
    actions_count += (*agents)[i]->actions_BDD_length();
  }
	
	// Allocate variables to each agent (states/variables + actions). This is setting the indices in each agent
  int k1 = 0;
  int k2 = 0;
  for (unsigned int i = 0; i < agents->size(); i++) { 
    k1 = (*agents)[i]->allocate_BDD_2_variables(k1);
    k2 = (*agents)[i]->allocate_BDD_2_actions(k2);
  }

	// Create Vtree
	SddLiteral var_count = 2 * states_count + actions_count;
	SddLiteral* var_order = get_var_order(options["ordering"], agents);

	Vtree* vtree;
	switch(options["vtree"]) {
		case 1:
			vtree = sdd_vtree_new_with_var_order(var_count, var_order, "right");
			break;
		case 2:
			vtree = sdd_vtree_new_with_var_order(var_count, var_order, "left");
			break;
		case 3:
			vtree = sdd_vtree_new_with_var_order(var_count, var_order, "balanced");
			break;	
		default: 
			cout << "Vtree of type " << options["vtree"] << " is not specified." << endl;
			exit(0);
	}


//	sdd_vtree_save_as_dot("vtree.dot", vtree);
	
	// Create and setup SDD manager
	int auto_gc_and_minimize = 1; //1=yes
	SddManager* manager = sdd_manager_new(vtree);
	if(options["dao"])
		sdd_manager_auto_gc_and_minimize_on(manager);
	/*sdd_manager_set_lr_size_limit(1.1, manager);
	sdd_manager_set_rr_size_limit(1.1, manager);
	sdd_manager_set_sw_size_limit(1.1, manager);
	*/
	//SddManager* manager = sdd_manager_create(var_count, auto_gc_and_minimize);
//	cout << "The manager has size " << sdd_manager_size(manager) << "(dead " << sdd_manager_live_size(manager) <<  ", live " << sdd_manager_dead_size(manager) << ")" << endl;
//	cout << "The manager has count " << sdd_manager_count(manager)  << "(dead " << sdd_manager_live_count(manager) <<  ", live " << sdd_manager_dead_count(manager) << ")" << endl;
	
	// Compute parameters
	struct parameters* params = new parameters;	
	params->action_variable_sdds = compute_action_variable_sdds(manager); 
	params->variable_sdds = compute_variable_sdds(manager);
	params->primed_variable_sdds = compute_primed_variable_sdds(manager);

	//what is this doing?	
  obsvars_bdd_length = (*agents)[0]->obsvars_BDD_length();
  envars_bdd_length = (*agents)[0]->get_var_index_end() + 1;

	print_params(params);

	// Compute transition relation SDD for each agent
  vector<SddNode*>* transition_relation_sdds = new vector<SddNode*>;
	SddNode* temp = 0;
	for (unsigned int i = 0; i < agents->size(); i++) {
		// encode protocol into SDD protocol_sdd
		cout << "Encoding the protocol for " << (*agents)[i]->get_name() << endl;
		SddNode* protocol_sdd = (*agents)[i]->encode_protocol(manager, params);
		sdd_ref(protocol_sdd, manager);
		cout << " - Done. " << endl;

		// encode evolution into SDD evolution_sdd
		cout << "Encoding the evolution for " << (*agents)[i]->get_name() << endl;
		SddNode* evolution_sdd = (options["smv"] == 0) ?
																 (*agents)[i]->encode_evolution(manager, params) : 
																 (*agents)[i]->encode_evolution_smv(manager, params) ;
		sdd_ref(evolution_sdd, manager);
		cout << " - Done. " << endl;


			cout << "the count of  evolution is " << sdd_count(evolution_sdd) << endl;

	
		// add (protocol_sdd && evolution_sdd) to transition_relation_vector
		SddNode* agent_transition_relation_sdd = sdd_conjoin(protocol_sdd, evolution_sdd, manager);
		sdd_ref(agent_transition_relation_sdd, manager);
		sdd_deref(evolution_sdd, manager);
		sdd_deref(protocol_sdd, manager);
		transition_relation_sdds->push_back(agent_transition_relation_sdd);
	}
	params->transitions = transition_relation_sdds;	
//	cout << "The manager has size " << sdd_manager_size(manager) << "(dead " << sdd_manager_live_size(manager) <<  ", live " << sdd_manager_dead_size(manager) << ")" << endl;
//	cout << "The manager has count " << sdd_manager_count(manager)  << "(dead " << sdd_manager_live_count(manager) <<  ", live " << sdd_manager_dead_count(manager) << ")" << endl;
	

	// Make SDD for initial states 
	cout << "Computing initial states" << endl;
	SddNode* initial_states_sdd = is_istates->encode_sdd(manager, params);
	sdd_ref(initial_states_sdd, manager);
	cout << " - Done." << endl;

	cout << "The manager has size " << sdd_manager_size(manager) << "(dead " << sdd_manager_live_size(manager) <<  ", live " << sdd_manager_dead_size(manager) << ")" << endl;
	cout << "The manager has count " << sdd_manager_count(manager)  << "(dead " << sdd_manager_live_count(manager) <<  ", live " << sdd_manager_dead_count(manager) << ")" << endl;
	
	// Compute full transition relation
/*	cout << "Computing full transition relation";
	SddNode* full_transition_relation = sdd_manager_true(manager);	
	cout << "A" << endl;
	for(unsigned int i = 0; i < transition_relation_sdds->size(); i++) {
		cout << "B" << endl;
		full_transition_relation = sdd_conjoin(full_transition_relation, (*transition_relation_sdds)[i], manager);
	}
	cout << "C" << endl;
	cout << "- Done." << endl;
*/
	

	// Compute Reachable States
	sdd_manager_garbage_collect(manager);
	cout << "Computing reachable state space" << endl;
	SddNode* reachable_state_sdd = compute_reach(initial_states_sdd, manager, params, transition_relation_sdds);
	sdd_ref(reachable_state_sdd, manager);
	params->reach = reachable_state_sdd;
	cout << " - Done." << endl;

	cout << "The count of reach is " << sdd_count(reachable_state_sdd) << endl; 

//	cout << "Model count of reach SDD: " << sdd_model_count(reachable_state_sdd, manager) << endl;
	
//	cout << "The manager has size " << sdd_manager_size(manager) << "(dead " << sdd_manager_live_size(manager) <<  ", live " << sdd_manager_dead_size(manager) << ")" << endl;
//	cout << "The manager has count " << sdd_manager_count(manager)  << "(dead " << sdd_manager_live_count(manager) <<  ", live " << sdd_manager_dead_count(manager) << ")" << endl;
	
	// Deal with fairness constraints
  if (!is_fairness->empty()) {
    cout << "Building set of fair states" << endl;
    for (vector< fairness_expression * >::iterator it =
           is_fairness->begin(); it != is_fairness->end(); it++) {
      SddNode* fairset = (*it)->check_formula(manager, params);
			sdd_ref(fairset, manager);
      (*it)->set_sdd_representation(fairset);
		}
		tmp = params->reach;
    params->reach = check_EG_fair(sdd_manager_true(manager), manager, params);
		sdd_ref(params->reach, manager);
		sdd_deref(tmp, manager);
    initial_states_sdd = sdd_conjoin(tmp = initial_states_sdd, params->reach, manager);
		sdd_ref(initial_states_sdd, manager);
		sdd_deref(tmp, manager);
		cout << " - Done." << endl;
  }      

	// check for deadlocks (AGEX(True)?)
	// check for arithmetic overflow

	// check formulae
    string str = "_init";
    (*is_evaluation)[str] = is_istates;
    modal_formula *init = new modal_formula(new atomic_proposition(&str));

   for (unsigned int i = 0; i < is_formulae->size(); i++) {
			cout << "Checking  " << ((*is_formulae)[i]).to_string() << "..." << endl;
     
      modal_formula f(4, init, &((*is_formulae)[i]));
			SddNode* result = f.check_formula(manager, params);
			sdd_ref(result, manager);

			bool satisfaction = result == params->reach;
			cout << "Formula " << i+1 << " is " << (satisfaction ? "TRUE" : "FALSE") << " in the model." << endl;
			sdd_deref(result, manager);
	} 
//	cout << "The manager has size " << sdd_manager_size(manager) << "(dead " << sdd_manager_live_size(manager) <<  ", live " << sdd_manager_dead_size(manager) << ")" << endl;
//	cout << "The manager has count " << sdd_manager_count(manager)  << "(dead " << sdd_manager_live_count(manager) <<  ", live " << sdd_manager_dead_count(manager) << ")" << endl	;
	//sdd_manager_print(manager);
	

	cout << "Freeing SDD manager." << endl;
	sdd_manager_free(manager);

    struct timeb tmb1;
    ftime(&tmb1);
    cout << "execution time = " << ((tmb1.time-tmb.time) + (tmb1.millitm-tmb.millitm)/1000.0) << endl;

  cout << "THE END" << endl;

}


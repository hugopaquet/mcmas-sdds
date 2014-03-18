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
    if (obsvars != NULL && obsvars->size() > 0)
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

void print_params(struct parameters * params) 
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
	// TODO rename BDD functions
	for (unsigned int i = 0; i < agents->size(); i++) {
 	  states_count += (*agents)[i]->state_BDD_length();
    actions_count += (*agents)[i]->actions_BDD_length();
  }

	// Allocate variables to each agent (states/variables + actions). This is setting the indices in each agens
  int k1 = 0;
  int k2 = 0;
  for (unsigned int i = 0; i < agents->size(); i++) { 
    k1 = (*agents)[i]->allocate_BDD_2_variables(k1);
    k2 = (*agents)[i]->allocate_BDD_2_actions(k2);
  }

	// Create and setup SDD manager
	SddLiteral var_count = 2 * states_count + actions_count;
	int auto_gc_and_minimize = 0; //1=yes
	SddManager* manager = sdd_manager_create(var_count,auto_gc_and_minimize);


	// Compute vector "a" = action_variable_sdds
	struct parameters* params = new parameters;	
	params->action_variable_sdds = compute_action_variable_sdds(manager); 
	params->variable_sdds = compute_variable_sdds(manager);
	params->primed_variable_sdds = compute_primed_variable_sdds(manager);

	print_params(params);

	// Compute transition relation SDD for each agent
	
  vector<SddNode*>* transition_relation_sdds = new vector<SddNode*>;
	
	for (unsigned int i = 0; i < agents->size(); i++) {
		// encode protocol into SDD protocol_sdd
		SddNode* protocol_sdd = (*agents)[i]->encode_protocol(manager, params);

		// encode evolution into SDD evolution_sdd
		SddNode* evolution_sdd = (*agents)[i]->encode_evolution(manager, params);
		// add protocol_sdd && evolution_sdd to transition_relation_vector
		SddNode* agent_transition_relation_sdd = sdd_conjoin(protocol_sdd, evolution_sdd, manager);
		transition_relation_sdds->push_back(agent_transition_relation_sdd);
		if(i == 1) 
			sdd_save_as_dot("sdd.dot", agent_transition_relation_sdd);
	}

	// Make SDD for initial states 
	SddNode* initial_states_sdd = is_istates->encode_sdd(manager, params);
	sdd_save_as_dot("istates.dot", initial_states_sdd);

	// Compute Reachable States
	




	sdd_manager_free(manager);


  cout << "THE END" << endl;

}


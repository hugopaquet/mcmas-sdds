#include "utilities.hh"


int
search_string_table(string * s)
{
  for (unsigned int i = 0; i < string_table->size(); i++)
    if (s->compare(*(*string_table)[i]) == 0)
      return i;
  return -1;
}

int
search_variable_table(variable * v)
{
  for (unsigned int i = 0; i < variable_table->size(); i++)
    if (v->equal_to((*variable_table)[i]))
      return i;
  return -1;
}

int
search_logic_expression_table(bool_expression * le)
{
  for (unsigned int i = 0; i < logic_expression_table->size(); i++)
    if (le->equal_to((*logic_expression_table)[i]))
      return i;
  return -1;
}
int
search_logic_expression_table(expression * e1, expression * e2)
{
  for (unsigned int i = 0; i < logic_expression_table->size(); i++)
    if (((*logic_expression_table)[i])->equal_to(e1, e2))
      return i;
  return -1;
}

int
search_logic_expression_table1(bool_expression * le)
{
  for (unsigned int i = 0; i < logic_expression_table1->size(); i++)
    if (le->equal_to((*logic_expression_table1)[i]))
      return i;
  return -1;
}

int
search_logic_expression_table1(expression * e1, expression * e2)
{
  for (unsigned int i = 0; i < logic_expression_table1->size(); i++)
    if (((*logic_expression_table1)[i])->equal_to(e1, e2))
      return i;
  return -1;
}

SddNode* 
check_EG(SddNode* p, SddManager* manager, struct parameters* params)
{
  // Computes the fixpoint iterating false
  if(is_fairness->empty()) {
		SddNode* tmp = sdd_manager_false(manager);
		SddNode* q = sdd_manager_true(manager);
 		while (q != tmp) {
      tmp = q;
      SddNode* x = check_EX(tmp, manager, params);
      q = sdd_conjoin(p, x, manager);
    } 
    return q;
  }  else
   	  return check_EG_fair(p, manager, params); 
			 
}

SddNode*
check_EF(SddNode* p, SddManager* manager, struct parameters* params)
{
  // Computes the fixpoint iterating false
	SddNode* tmp = sdd_manager_true(manager);
  SddNode* q = sdd_manager_false(manager);
	int iter = 0;
  while (q != tmp) {
		if(iter == 1)
			sdd_save_as_dot("q.dot", q);
    tmp = q;
    q = sdd_disjoin(p, check_EX(tmp, manager, params), manager);
		iter++;
  }
  return sdd_conjoin(q, params->reach, manager);
}


SddNode* 
check_EX(SddNode* next, SddManager* manager, struct parameters* params)
{
  // Computes the preimage
/*  if(options["nobddcache"] == 0) {
    if (para->calReachRT) {
      BDD reachRT1 = *para->reach;
      for (unsigned int i = 0; i < agents->size(); i++)
        reachRT1 *= (*para->vRT)[i];
      para->reachRT = new BDD(reachRT1);
      para->calReachRT = false;
    }
  } */
	unsigned int v = params->variable_sdds->size(); // number of state variables
	unsigned int a = params->action_variable_sdds->size(); // number of action variables		
	SddLiteral map[2 * v + a + 1]; 
	for(unsigned int i = 1; i <= v; i++) {	
		map[i] = sdd_node_literal((*params->primed_variable_sdds)[i-1]); 
	}
	for(unsigned int i = v + 1; i <= 2 * v; i++) {
		map[i] = sdd_node_literal((*params->primed_variable_sdds)[i - v - 1]); 
	}
	for(unsigned int i = 2 * v + 1; i <= 2 * v + a; i++) {
		map[i] = sdd_node_literal((*params->action_variable_sdds)[i - 2 * v - 1]); 
	}

	SddNode* result = sdd_rename_variables(next, map, manager);
/*  if(options["nobddcache"] == 0)
    result = result * (*para->reachRT);
  else { */
    for (unsigned int i = 0; i < agents->size(); i++)
      result = sdd_conjoin(result, (*params->transitions)[i], manager);
//  }
	for(unsigned int i = 0; i < v; i++) {
		result = sdd_exists(sdd_node_literal((*params->primed_variable_sdds)[i]), result, manager);
	}
	for(unsigned int i = 0; i < a; i++) {
	  result = sdd_exists(sdd_node_literal((*params->action_variable_sdds)[i]), result, manager);
	}
	result = sdd_conjoin(result, params->reach, manager);
  return result;
}

SddNode*
check_EU(SddNode* p, SddNode* q, SddManager* manager, struct parameters* params)
{                               // See Huth-Ryan, pag. 180
  SddNode* W = p;
  SddNode* X = params->reach;
  SddNode* Y = q;
  while (X != Y) {
    X = Y;
    Y = sdd_disjoin(Y, sdd_conjoin(W,  check_EX(Y, manager, params), manager), manager);
  }
  return Y;
}


SddNode*
check_AU(SddNode* p, SddNode* q, SddManager* manager, struct parameters* params)
{                               // Tricky one, see Huth Ryan pag. 167 and 179
	SddNode* notq = sdd_negate(q, manager);
	SddNode* notp = sdd_negate(p, manager);
  SddNode* result =
    sdd_conjoin(sdd_negate(sdd_disjoin(check_EU(notq, sdd_conjoin(notp, notq, manager), manager, params), check_EG(notq, manager, params), manager), manager), params->reach, manager);
  return result;
}


SddNode*
check_GK(SddNode* next, string name, SddManager* manager, struct parameters* params)
{
  set < string > gi = (*is_groups)[name];
  SddNode* tmp = sdd_manager_false(manager);
	SddNode* ntmp = sdd_conjoin(params->reach, sdd_negate(next, manager), manager); // possible problem: check "-" = "and not"
  for (set < string >::iterator igs = gi.begin(); igs != gi.end(); igs++) {
    basic_agent *agent = (*is_agents)[*igs];
    tmp = sdd_disjoin(tmp, agent->project_local_state(ntmp, manager, params), manager);
  }
  tmp = sdd_conjoin(params->reach, sdd_negate(tmp, manager), manager);
  return tmp;
}


SddNode*
check_GCK(SddNode* next, string name, SddManager* manager, struct parameters* params)
{
  // GCK p = GK(p * GCK(p)) see fhmv:rak, section 11.5
  SddNode* tmp = params->reach;
  SddNode* tmp2 = next;
  set < string > gi = (*is_groups)[name];
  while (tmp != tmp2) {
    tmp2 = tmp;
    tmp = sdd_conjoin(next, tmp, manager);
    SddNode* ntmp = sdd_conjoin(params->reach, sdd_negate(tmp, manager), manager);	
    tmp = sdd_manager_false(manager);
    for (set < string >::iterator igs = gi.begin(); igs != gi.end(); igs++) {
      basic_agent *agent = (*is_agents)[*igs];
			SddNode* projection = agent->project_local_state(ntmp, manager, params);
      tmp = sdd_disjoin(tmp, projection, manager);
    }
    tmp = sdd_conjoin(params->reach, sdd_negate(tmp, manager), manager);
  }
  return tmp;
}


/*
BDD
check_EG_fair(BDD p, bdd_parameters * para)
{
  // Computes the fixpoint iterating false
  // See "Efficient generation of counterexamples and witnesses in
  // symbolic model checking", Clarke Grumberg McMillan Zhao, 1995
  // Section 4, p.3
  BDD tmp = para->bddmgr->bddZero();
  BDD q = para->bddmgr->bddOne();
  BDD fc_bdd = para->bddmgr->bddOne();
  while (q != tmp) {
    tmp = q;
    for (vector < fairness_expression * >::iterator fi =
           is_fairness->begin(); fi != is_fairness->end(); fi++) {
      BDD hf = (*fi)->get_bdd_representation(); // The BDD for the fairness constraint
      BDD tmp1 = check_EU(p, q * hf, para);
      fc_bdd = fc_bdd * check_EX(tmp1, para);
    }
    q = p * fc_bdd;
  }
  return q;
}

BDD
check_EG_fair_Qh(BDD p, bdd_parameters * para, vector< vector < BDD* >* >* Qh) 
{
  if(Qh->empty()) {
    for(unsigned int k=0; k<is_fairness->size(); k++) 
      Qh->push_back(new vector< BDD* >());
  }
  
  BDD tmp = para->bddmgr->bddZero();
  BDD q = para->bddmgr->bddOne();
  BDD fc_bdd = para->bddmgr->bddOne();
  //int x = 0;
  while (q != tmp) {
    tmp = q;
    //x = 0;
    for (unsigned int k=0; k<is_fairness->size(); k++) {
      BDD hf = (*is_fairness)[k]->get_bdd_representation(); // The BDD for the fairness constraint
      vector< BDD* >* qh = (*Qh)[k];
      if(!qh->empty()) {
				for(unsigned int j=0; j<qh->size(); j++) {
					BDD* t = qh->back();
					qh->pop_back();
					delete t;
				}
      }
      BDD tmp1 = check_EU_Qh(p, q * hf, para, qh);
      fc_bdd = fc_bdd * check_EX(tmp1, para);
      //x++;
    }
    q = p * fc_bdd;
  }
  return q;
}

BDD
check_EF_fair(BDD p, BDD fair_reach, bdd_parameters * para)
{
  return check_EU_fair(*para->reach, p, fair_reach, para);
}

BDD
check_EX_fair(BDD p, BDD fair_reach, bdd_parameters * para)
{
  return check_EX(p * fair_reach, para);
}

BDD
check_EU_fair(BDD p, BDD q, BDD fair_reach, bdd_parameters * para)
{
  return check_EU(p * fair_reach, q * fair_reach, para);
}

BDD
check_nO_fair(BDD next, string name, BDD fair_reach, bdd_parameters * para)
{
  // Check deontic
  next = next.SwapVariables(*para->v, *para->pv);       // Now it's the next state
  BDD RO = (*is_agents)[name]->encode_greenstates(para);
  BDD result = Exists(para->bddmgr, para->pv, RO * next * fair_reach);  // States from which...
  return result;
}

BDD
check_GK_fair(BDD next, string name, BDD fair_reach, bdd_parameters * para)
{
  set < string > gi = (*is_groups)[name];
  BDD tmp = para->bddmgr->bddZero();
  BDD ntmp = fair_reach - next;
  for (set < string >::iterator igs = gi.begin(); igs != gi.end(); igs++) {
    basic_agent *agent = (*is_agents)[*igs];
    tmp += agent->project_local_state(&ntmp, para->bddmgr, para->v);
  }
  tmp = (*para->reach) - tmp;
  return tmp;
}

BDD
check_DK_fair(BDD next, string name, BDD fair_reach, bdd_parameters * para)
{
  set < string > gi = (*is_groups)[name];
  BDD tmp = para->bddmgr->bddOne();
  BDD ntmp = fair_reach - next;
  for (set < string >::iterator igs = gi.begin(); igs != gi.end(); igs++) {
    basic_agent *agent = (*is_agents)[*igs];
    tmp *= agent->project_local_state(&ntmp, para->bddmgr, para->v);
  }
  tmp = (*para->reach) - tmp;
  return tmp;
}

BDD
check_GCK_fair(BDD next, string name, BDD fair_reach,
               bdd_parameters * para)
{
  // GCK p = GK(p * GCK(p)) see fhmv:rak, section 11.5
  BDD tmp = *para->reach;
  BDD tmp2 = next;
  set < string > gi = (*is_groups)[name];
  while (tmp != tmp2) {
    tmp2 = tmp;
    tmp = next * tmp;
    BDD ntmp = fair_reach - tmp;
    tmp = para->bddmgr->bddZero();
    for (set < string >::iterator igs = gi.begin(); igs != gi.end(); igs++) {
      basic_agent *agent = (*is_agents)[*igs];
      tmp += agent->project_local_state(&ntmp, para->bddmgr, para->v);
    }
    tmp = (*para->reach) - tmp;
  }
  return tmp;
}

BDD
get_K_states(BDD aset1, BDD * state, string name, bdd_parameters * para)
{
  basic_agent *agent = (*is_agents)[name];
  BDD localstate = agent->project_local_state(state, para->bddmgr, para->v);
  return aset1 * localstate;
}

*/
SddNode*
get_nK_states(SddNode * state, string name, SddManager* manager, struct parameters* params)
{

  basic_agent *agent = (*is_agents)[name];
	SddNode* localstate = agent->project_local_state(state, manager, params);
  return sdd_conjoin(params->reach, localstate, manager);
}
/*
BDD
get_nK_states_fair(BDD * state, string name, BDD fair_reach,
                   bdd_parameters * para)
{
  basic_agent *agent = (*is_agents)[name];
  BDD localstate = agent->project_local_state(state, para->bddmgr, para->v);
  return fair_reach * localstate;
}

BDD
get_GK_states(BDD aset1, BDD * state, string name, bdd_parameters * para)
{
  BDD tmpaset1 = para->bddmgr->bddZero();
  set < string > names_g = (*is_groups)[name];
  for (set < string >::iterator igs = names_g.begin(); igs != names_g.end();
       igs++) {
    basic_agent *agent = (*is_agents)[*igs];
    BDD localstate = agent->project_local_state(state, para->bddmgr, para->v);
    tmpaset1 = tmpaset1 + (aset1 * localstate);
  }
  return tmpaset1;
}

BDD
get_DK_states(BDD aset1, BDD * state, string name, bdd_parameters * para)
{
  BDD tmpaset1 = aset1;
  set < string > names_g = (*is_groups)[name];
  for (set < string >::iterator igs = names_g.begin(); igs != names_g.end();
       igs++) {
    basic_agent *agent = (*is_agents)[*igs];
    BDD localstate = agent->project_local_state(state, para->bddmgr, para->v);
    tmpaset1 = tmpaset1 * localstate;
  }
  return tmpaset1;
}
*/

SddNode*
check_EG_fair(SddNode* p, SddManager* manager, struct parameters* params)
{
	SddNode* tmp = sdd_manager_false(manager);
	SddNode* q = sdd_manager_true(manager);
	SddNode* fc_sdd = sdd_manager_true(manager);
	while (q != tmp) {
		tmp = q;
		for (vector <fairness_expression*>::iterator fi = is_fairness->begin(); fi != is_fairness->end(); fi++) {
			SddNode* hf = (*fi)->get_sdd_representation();
			SddNode* tmp1 = check_EU(p, sdd_conjoin(q, hf, manager), manager, params);
			fc_sdd = sdd_conjoin(fc_sdd, check_EX(tmp1, manager, params), manager);		
		}

    q = sdd_conjoin(p, fc_sdd, manager);
	}
  return q;
}

void 
get_literals(SddNode* node, vector<SddLiteral>* literals) {
	if(sdd_node_is_literal(node)) {
		SddLiteral literal = sdd_node_literal(node);
		if(literal < 0) 
			literal = -literal;
		bool found = false;
		for(unsigned int i = 0; i < literals->size(); i++)
			if((*literals)[i] == literal) {
				found = true;
			}
		if(!found) {
			literals->push_back(literal);
		}
	}
	else if(sdd_node_is_decision(node)) {
		SddNodeSize size = sdd_node_size(node);
		SddNode** children = sdd_node_elements(node);
		for(unsigned int i = 0; i < 2*size; i++)
			get_literals(children[i], literals);
	}
}

string
to_string(SddNode* node) {
	string alphabet[] = {"n", "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R"} ;
	if(sdd_node_is_true(node))
			return "1";
		if(sdd_node_is_false(node))
		return "0";
 	if(sdd_node_is_literal(node)) {
		int n = sdd_node_literal(node);
		if (n < 0) {
 			return "(~" + alphabet[-n] + ")";  
		}

		return alphabet[n]; // set 'Re
	}
	string result = "";
	for (unsigned int i = 0; i < sdd_node_size(node); i++) {
		result = (result != "" ? (result + "|((") : "((") + to_string((sdd_node_elements(node))[2*i]) 
									+ ")&(" + to_string((sdd_node_elements(node))[2*i + 1]) + "))"; 
	}
	return result;
}

void 
save_to_string(SddNode* node) {
	string s = to_string(node);
	ofstream out("sdd_output.txt");
	out << s;
}




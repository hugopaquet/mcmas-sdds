#include <ctime>
#include "types.hh"
#include "utilities.hh"
extern "C" {
	#include "sddapi.h"
}

using namespace std;

basic_agent::basic_agent(string * n,
                         map< string, variable * >*lv,
                         map< string, basictype * >*v0,
                         vector< basictype * >*vecv0,
                         map< string, basictype * >*v1,
                         vector< basictype * >*vecv1,
                         bool_expression * r,
                         set< string > *v2,
                         vector< protocol_line * >*v3,
                         vector< evolution_line * >*v4)
{
  name = n;
  lobsvars = lv;
  obsvars = v0;
  vars = v1;
  vec_obsvars = vecv0;
  vec_vars = vecv1;
  actions = v2;
  protocol = v3;
  evolution = v4;
  redstates = r;
  action_indices = new map< string, vector< bool > *>;
  generate_action_bdd_value();
}

basic_agent::~basic_agent()
{
	if(lobsvars) {
		for(map< string, variable * >::iterator i=lobsvars->begin(); i!=lobsvars->end(); i++)
			delete i->second;
		delete lobsvars;
	}
	if(obsvars) {
		for(map< string, basictype * >::iterator i=obsvars->begin(); i!=obsvars->end(); i++)
			delete i->second;
		delete obsvars;
		delete vec_obsvars;
	}
	if(vars) {
		for(map< string, basictype * >::iterator i=vars->begin(); i!=vars->end(); i++)
			delete i->second;
		delete vars;
		delete vec_vars;
	}
	if(redstates)
		delete redstates;
	if(actions)
		delete actions;
	if(protocol) {
		for(unsigned int i=0; i<protocol->size(); i++)
			delete (*protocol)[i];
		delete protocol;
	}
	if(evolution) {
		for(unsigned int i=0; i<evolution->size(); i++)
			delete (*evolution)[i];
		delete evolution;
	}
}

string
basic_agent::get_name()
{
  if (name == NULL) {
    cout << " error: name in agent is undefined!" << endl;
    exit(1);
  } else
    return *name;
}

string *
basic_agent::get_name_point()
{
  return name;
}	

map< string, basictype * >*basic_agent::get_obsvars()
{
  return obsvars;
}

vector< basictype * >*basic_agent::get_vec_obsvars()
{
  return vec_obsvars;
}

vector< basictype * >*basic_agent::get_vec_vars()
{
  return vec_vars;
}

map< string, variable * >*basic_agent::get_lobsvars()
{
  return lobsvars;
}

map< string, basictype * >*basic_agent::get_vars()
{
  return vars;
}

basictype *
basic_agent::get_basictype_by_name(string varname)
{
  if (obsvars != NULL) {
    if (obsvars->find(varname) != obsvars->end())
      return (*obsvars)[varname];
  }
  if (vars != NULL) {
    if (vars->find(varname) != vars->end())
      return (*vars)[varname];
  }
  return NULL;
}

set< string > *basic_agent::get_actions()
{
  return actions;
}

vector< protocol_line * >*basic_agent::get_protocol()
{
  return protocol;
}

vector< evolution_line * >*basic_agent::get_evolution()
{
  return evolution;
}

bool_expression *
basic_agent::get_redstates()
{
  return redstates;
}

string
basic_agent::to_string()
{
  string str = "Agent " + *name + "\n";

  if (obsvars != NULL && obsvars->size() > 0) {
    str += "Obsvars:\n";
    for (map< string, basictype * >::iterator i = obsvars->begin();
         i != obsvars->end(); i++)
      str += "    " + (*i).second->to_string() + ";\n";
    str += "end Obsvars\n";
  }

  str += "Vars:\n";
  for (map< string, basictype * >::iterator i = vars->begin();
       i != vars->end(); i++)
    str += "    " + (*i).second->to_string() + ";\n";
  str += "end Vars\nRedStates:\n    ";
  if (redstates == NULL)
    str += "";
  else
    str += redstates->to_string() + ";";
  str += "\nend RedStates\nActions = { ";
  unsigned int k = 0;
  unsigned int bound = (unsigned int) actions->size() - 1;
  for (set< string >::iterator i = actions->begin(); i != actions->end();
       i++) {
    if (k == bound)
      str += *i + " ";
    else
      str += *i + ", ";
    k++;
  }
  str += "}\nProtocol:\n";
  for (vector< protocol_line * >::iterator i = protocol->begin();
       i != protocol->end(); i++)
    str += "    " + (*i)->to_string() + ";\n";
  str += "end Protocol\nEvolution:\n";
  for (vector< evolution_line * >::iterator i = evolution->begin();
       i != evolution->end(); i++)
    str += "    " + (*i)->to_string() + ";\n";
  str += "end Evolution\n";
  str += "end Agent\n";
  return str;
}

int
basic_agent::state_BDD_length()
{
  int count = 0;
  count += obsvars_BDD_length();
  if (vars != NULL)
    for (map< string, basictype * >::iterator i = vars->begin();
         i != vars->end(); i++)
      count += (*i).second->BDD_length();
  return count;
}

int
basic_agent::obsvars_BDD_length()
{
  int count = 0;
  if (obsvars != NULL)
    for (map< string, basictype * >::iterator i = obsvars->begin();
         i != obsvars->end(); i++)
      count += (*i).second->BDD_length();
  return count;
}

unsigned int
basic_agent::actions_BDD_length()
{
  if (actions == NULL || actions->size() == 0)
    return 0;
  return log_2((unsigned int) actions->size());
}

void
basic_agent::set_action_index_begin(int i)
{
  action_index_begin = i;
}

void
basic_agent::set_action_index_end(int i)
{
  action_index_end = i;
}

void
basic_agent::set_var_index_begin(int i)
{
  var_index_begin = i;
}

void
basic_agent::set_var_index_end(int i)
{
  var_index_end = i;
}

int
basic_agent::get_action_index_begin()
{
  return action_index_begin;
}

int
basic_agent::get_action_index_end()
{
  return action_index_end;
}

int
basic_agent::get_var_index_begin()
{
  return var_index_begin;
}

int
basic_agent::get_var_index_end()
{
  return var_index_end;
}

void
basic_agent::generate_action_bdd_value()
{
  int size = actions_BDD_length();
  if (size == 0)
    return;
  vector< bool > base(size, false);
  for (set< string >::iterator i = actions->begin(); i != actions->end();
       i++) {
    vector< bool > *temp = new vector< bool > (base);
    pair < string, vector< bool > *>p(*i, temp);
    action_indices->insert(p);
    for (int j = size - 1; j >= 0; j--) {
      if (base[j])
        base[j] = false;
      else {
        base[j] = true;
        break;
      }
    }
  }
}


void
basic_agent::print_value_index()
{
  for (map< string, vector< bool > *>::iterator i = action_indices->begin();
       i != action_indices->end(); i++) {
    cout << i->first << ": ";
    for (unsigned int j = 0; j < i->second->size(); j++)
      cout << ((*(i->second))[j] ? 1 : 0);
    cout << endl;
  }
}

map< string, vector< bool > *>*basic_agent::get_action_indices()
{
  return action_indices;
}

int
basic_agent::allocate_BDD_2_variables(int start)
{
  set_var_index_begin(start);
  int count = start;

  if (vec_obsvars != NULL)
    for (unsigned int i = 0; i < vec_obsvars->size(); i++) {
      int l = (*vec_obsvars)[i]->BDD_length();
      (*vec_obsvars)[i]->set_index_begin(count);
      (*vec_obsvars)[i]->set_index_end(count + l - 1);
      count += l;
    }
  if (vec_vars != NULL)
    for (unsigned int i = 0; i < vec_vars->size(); i++) {
      int l = (*vec_vars)[i]->BDD_length();
      (*vec_vars)[i]->set_index_begin(count);
      (*vec_vars)[i]->set_index_end(count + l - 1);
      count += l;
    }

  set_var_index_end(count - 1);
  return count;
}

int
basic_agent::allocate_BDD_2_actions(int start)
{
  set_action_index_begin(start);
  int end = start + actions_BDD_length();
  set_action_index_end(end - 1);
  return end;
}

SddNode* 
basic_agent::encode_action(SddManager * manager, string action_name, vector<SddNode*>* action_variable_sdds) 
{
  map< string, vector< bool > *>::iterator k = action_indices->find(action_name);
  if (k != action_indices->end()) {
    SddNode* encoding = sdd_manager_true(manager);
    vector< bool > *variable_vector = (*k).second;
    for (int i = action_index_begin; i <= action_index_end; i++) {
  	  encoding = sdd_conjoin(encoding, (*variable_vector)[i - action_index_begin] ? (*action_variable_sdds)[i] : sdd_negate((*action_variable_sdds)[i], manager), manager);
		}

    return encoding;
  } else 
	return 0;
}


SddNode* 
basic_agent::encode_protocol(SddManager * manager, struct parameters* params) 
{
	SddNode* tmp;
	SddNode* protocol_sdd = sdd_manager_false(manager);
  for (vector<protocol_line *>::iterator i = protocol->begin(); i != protocol->end(); i++) {
		SddNode* condition_sdd = sdd_manager_false(manager);
		bool_expression* condition = (*i)->get_condition();
		if(!condition->is_other_branch()) {
			condition_sdd = condition->encode_sdd(manager, params);
		} else {
			condition_sdd = sdd_manager_true(manager);
		}	
		sdd_ref(condition_sdd, manager);
		SddNode* actions_sdd = sdd_manager_false(manager); // start from condition rather than false? 
		for(set<string>::iterator j = (*i)->get_actions()->begin(); j != (*i)->get_actions()->end(); j++) {
			string action_name = (*j);
			actions_sdd = sdd_disjoin(tmp = actions_sdd, encode_action(manager, action_name, params->action_variable_sdds), manager);
			sdd_ref(actions_sdd, manager);
			sdd_deref(tmp, manager);
		}

		SddNode* line = sdd_conjoin(condition_sdd, actions_sdd, manager);
		sdd_ref(line, manager);
		sdd_deref(condition_sdd, manager);
		sdd_deref(actions_sdd, manager);
		protocol_sdd = sdd_disjoin(tmp = protocol_sdd, line, manager);	
		sdd_ref(protocol_sdd, manager);
		sdd_deref(line, manager);
		sdd_deref(tmp, manager);
	}

	return protocol_sdd;
}


SddNode* 
basic_agent::encode_evolution(SddManager * manager, struct parameters * params) 
{
	SddNode * tmp;
	SddNode * evolution_sdd = sdd_manager_false(manager);
	SddNode * lastcond_sdd = sdd_manager_true(manager);
	int k = 0;
  for (vector< evolution_line * >::iterator i = evolution->begin();
       i != evolution->end(); i++) {
    vector< assignment * >*assignments = (*i)->get_assignments();
    map< string, basictype * >*mp = new map< string, basictype * >;
  if (obsvars != NULL)
      for (map< string, basictype * >::iterator j = obsvars->begin();
           j != obsvars->end(); j++) {
        bool found = false;
        for (unsigned int k = 0; k < assignments->size(); k++) {
          variable *var = (*assignments)[k]->get_var();
          string varname = var->get_variable_name();
          if (varname == j->first) {
            found = true;
            break;
          }
        }
        if (!found)   // we add this variable to both sides
          mp->insert(*j);
      }
    if (vars != NULL)
      for (map< string, basictype * >::iterator j = vars->begin();
           j != vars->end(); j++) {
        bool found = false;
        for (unsigned int k = 0; k < assignments->size(); k++) {
          variable *var = (*assignments)[k]->get_var();
          string varname = var->get_variable_name();
          if (varname == j->first) {
            found = true;
            break;
          }
        }

        if (!found)   // we add this variable to both sides
          mp->insert(*j);
      }

    SddNode* assignment_sdd = (*i)->encode_sdd_assignments(manager, params);
		sdd_ref(assignment_sdd, manager);
    SddNode* condition_sdd = (*i)->encode_sdd_condition(manager, params);
		sdd_ref(condition_sdd, manager);

		for (map< string, basictype * >::iterator j = mp->begin();
         j != mp->end(); j++) {
      int begin = j->second->get_index_begin();
      int end = j->second->get_index_end();
      for (int k = begin; k <= end; k++) {
				SddNode* tmp4 = sdd_disjoin(
																			(*params->variable_sdds)[k],
																			sdd_negate((*params->primed_variable_sdds)[k], manager),
																			manager);
				sdd_ref(tmp4, manager);
				SddNode* tmp3 = sdd_disjoin(
																			sdd_negate((*params->variable_sdds)[k], manager),
																		  (*params->primed_variable_sdds)[k],
																			manager);
				sdd_ref(tmp3, manager);
				SddNode* tmp2 = sdd_conjoin(
																	tmp3, 
																  tmp4,
																  manager);
				sdd_ref(tmp2, manager);
				sdd_deref(tmp3, manager);
				sdd_deref(tmp4, manager);
				assignment_sdd = sdd_conjoin(
															tmp = assignment_sdd, 
															tmp2,
															manager);
				sdd_ref(assignment_sdd, manager);
				sdd_deref(tmp2, manager);
				sdd_deref(tmp, manager);
		
      }

    }
		lastcond_sdd = sdd_conjoin(tmp = lastcond_sdd, sdd_negate(condition_sdd, manager), manager);
		sdd_ref(lastcond_sdd, manager);
		sdd_deref(tmp, manager);
		
		evolution_sdd = sdd_disjoin(tmp = evolution_sdd, sdd_conjoin(assignment_sdd, condition_sdd, manager), manager);	
		sdd_ref(evolution_sdd, manager);
		sdd_deref(tmp, manager);
		sdd_deref(assignment_sdd, manager);
		sdd_deref(condition_sdd, manager);

	}
	


	SddNode* dnc = sdd_manager_true(manager);
  int begin, end;
  if (obsvars != NULL)
    for (map< string, basictype * >::iterator i = obsvars->begin();
         i != obsvars->end(); i++) {
      basictype *var_type = (*i).second;
      begin = var_type->get_index_begin();
      end = var_type->get_index_end();	
      for (int j = begin; j <= end; j++) {
				SddNode* node3 =  sdd_disjoin((*params->variable_sdds)[j], 
											sdd_negate((*params->primed_variable_sdds)[j], manager), manager);
				sdd_ref(node3, manager);
				SddNode* node2 = sdd_disjoin(sdd_negate((*params->variable_sdds)[j], manager), 
											(*params->primed_variable_sdds)[j], manager);
				sdd_ref(node2, manager);
				SddNode* node1 = sdd_conjoin(node2, node3, manager);
				sdd_ref(node1, manager);
				sdd_deref(node2, manager);
				sdd_deref(node3, manager);
				dnc = sdd_conjoin(tmp = dnc, node1, manager);
				sdd_ref(dnc, manager);
				sdd_deref(node1, manager);
				sdd_deref(tmp, manager);
			}
    }
  if (vars != NULL) {
    for (map< string, basictype * >::iterator i = vars->begin();
         i != vars->end(); i++) {
      basictype *var_type = (*i).second;
      begin = var_type->get_index_begin();
      end = var_type->get_index_end();
      for (int j = begin; j <= end; j++) {
				SddNode* tmp3 = sdd_disjoin((*params->variable_sdds)[j], 
											sdd_negate((*params->primed_variable_sdds)[j], manager), manager);
				sdd_ref(tmp3, manager);
				SddNode* tmp2 = sdd_disjoin(sdd_negate((*params->variable_sdds)[j], manager), 
											(*params->primed_variable_sdds)[j], manager);
				sdd_ref(tmp2, manager);
				SddNode* tmp1 = sdd_conjoin(tmp2, tmp3, manager);
				sdd_ref(tmp1, manager);
				sdd_deref(tmp2, manager);
				sdd_deref(tmp3, manager);
				dnc = sdd_conjoin(tmp = dnc, tmp1, manager);
				sdd_ref(dnc, manager);
				sdd_deref(tmp, manager);
				sdd_deref(tmp1, manager);
			}
		}
	}
  
	lastcond_sdd = sdd_conjoin(tmp = lastcond_sdd, dnc, manager);
	sdd_ref(lastcond_sdd, manager);
	sdd_deref(tmp, manager);
  evolution_sdd =  sdd_disjoin(tmp = evolution_sdd, lastcond_sdd, manager);
	sdd_ref(evolution_sdd, manager);
	sdd_deref(lastcond_sdd, manager);
	sdd_deref(tmp, manager);
	return evolution_sdd;
}
 

SddNode* 
basic_agent::encode_evolution_smv(SddManager * manager, struct parameters * params) 
{
	SddNode* gc;
	bool env = get_name() == "Environment";
  vector< evolution_line * >tmpevol(evolution->begin(), evolution->end());
  map< string, SddNode* > tmpsdds;
  while (tmpevol.size() > 0) {
    evolution_line *evoline = tmpevol[0];
    tmpevol.erase(tmpevol.begin());
    vector< assignment * >*assignments = evoline->get_assignments();
    variable *var = (*assignments)[0]->get_var();
    string varname = var->get_variable_name();

    SddNode* sddassignment = evoline->encode_sdd_assignments(manager, params);
		sdd_ref(sddassignment, manager);
    SddNode* sddcondition = evoline->encode_sdd_condition(manager, params);
		sdd_ref(sddcondition, manager);
    SddNode* tmplast = sdd_negate(sddcondition, manager);
		sdd_ref(tmplast, manager);
    SddNode* linesdd = sdd_conjoin(sddassignment, sddcondition, manager);
		sdd_ref(linesdd, manager);
		sdd_deref(sddassignment, manager);
		sdd_deref(sddcondition, manager);
	
    unsigned int i = 0;
    while (i < tmpevol.size()) {
      evolution_line *evoline1 = tmpevol[i];
      vector< assignment * >*assignments1 = evoline1->get_assignments();
      variable *var1 = (*assignments1)[0]->get_var();
      if (varname.compare(var1->get_variable_name()) == 0) {
        SddNode* sddassignment1 = evoline1->encode_sdd_assignments(manager, params);
				sdd_ref(sddassignment1, manager);
        SddNode* sddcondition1 = evoline1->encode_sdd_condition(manager, params);
				sdd_ref(sddcondition1, manager);
        linesdd = sdd_disjoin(gc = linesdd, sdd_conjoin(sddassignment1, sddcondition1, manager), manager);
				sdd_ref(linesdd, manager);
				sdd_deref(gc, manager);
				sdd_deref(sddassignment1, manager);
        tmplast = sdd_conjoin(gc = tmplast, sdd_negate(sddcondition1, manager), manager);
				sdd_ref(tmplast, manager);
				sdd_deref(gc, manager);
				sdd_deref(sddcondition1, manager);
        tmpevol.erase(tmpevol.begin() + i);
      } else
        i++;
    }


    basictype *var_type = var->get_var_type();
    int begin = var_type->get_index_begin();
    int end = var_type->get_index_end();
    for (int j = begin; j <= end; j++) {
			SddNode* node1 = sdd_disjoin(sdd_negate((*params->variable_sdds)[j], manager), (*params->primed_variable_sdds)[j], manager);	
			sdd_ref(node1, manager);
			SddNode* node2 = sdd_disjoin((*params->variable_sdds)[j], sdd_negate((*params->primed_variable_sdds)[j], manager), manager);
			sdd_ref(node2, manager);
      tmplast = sdd_conjoin(gc = tmplast, sdd_conjoin(node1, node2, manager), manager);
			sdd_ref(tmplast, manager);
			sdd_deref(gc, manager);	
			sdd_deref(node1, manager);
			sdd_deref(node2, manager);
		}

    linesdd = sdd_disjoin(gc = linesdd, tmplast, manager);
		sdd_ref(linesdd, manager);
		sdd_deref(tmplast, manager);
		sdd_deref(gc, manager);
    tmpsdds[varname] = linesdd;

  }

	
  SddNode* dnc = sdd_manager_true(manager);
  int begin, end;
  if (obsvars != NULL)
    for (map< string, basictype * >::iterator i = obsvars->begin();
         i != obsvars->end(); i++) {
      if (tmpsdds.find(i->first) == tmpsdds.end()) {
        basictype *var_type = (*i).second;
        begin = var_type->get_index_begin();
        end = var_type->get_index_end();
        for (int j = begin; j <= end; j++) {
					SddNode* node1 = sdd_disjoin(sdd_negate((*params->variable_sdds)[j], manager), (*params->primed_variable_sdds)[j], manager);
					sdd_ref(node1, manager);
					SddNode* node2 = sdd_disjoin((*params->variable_sdds)[j], sdd_negate((*params->primed_variable_sdds)[j], manager), manager);
					sdd_ref(node2, manager);
				  dnc = sdd_conjoin(gc = dnc, sdd_conjoin(node1, node2, manager), manager);
					sdd_ref(dnc, manager);
					sdd_deref(gc, manager);
					sdd_deref(node1, manager);
					sdd_deref(node2, manager);
				}
      }
    }
  if (vars != NULL)
    for (map< string, basictype * >::iterator i = vars->begin();
         i != vars->end(); i++) {
      if (tmpsdds.find(i->first) == tmpsdds.end()) {
        basictype *var_type = (*i).second;
        begin = var_type->get_index_begin();
        end = var_type->get_index_end();
        for (int j = begin; j <= end; j++) {
					SddNode* node1 = sdd_disjoin(sdd_negate((*params->variable_sdds)[j], manager), (*params->primed_variable_sdds)[j], manager);
					sdd_ref(node1, manager);
					SddNode* node2 = sdd_disjoin((*params->variable_sdds)[j], sdd_negate((*params->primed_variable_sdds)[j], manager), manager);
					sdd_ref(node2, manager);
		      dnc = sdd_conjoin(gc = dnc, sdd_conjoin(node1, node2, manager), manager);
					sdd_ref(dnc, manager);
					sdd_deref(gc, manager);
					sdd_deref(node1, manager);
					sdd_deref(node2, manager);
				}
      }
    }

  for (map< string, SddNode* >::iterator i = tmpsdds.begin(); i != tmpsdds.end();
       i++) {
 	  dnc = sdd_conjoin(gc = dnc, i->second, manager);
		sdd_ref(dnc, manager);
		sdd_deref(gc, manager);
	}
  return dnc;	
}


set< string > *basic_agent::get_obs_enum_values()
{
  if (obsvars != NULL) {
    set< string > *tmpset = new set< string >;
    for (map< string, basictype * >::iterator i = obsvars->begin();
         i != obsvars->end(); i++)
      if (i->second->get_type() == 3) {
        set< string > *varset = ((enumerate *) (i->second))->get_enumvalue();
        tmpset->insert(varset->begin(), varset->end());
      }
    return tmpset;
  }
  return NULL;
}

bool
basic_agent::check_var_against_enum_values(set< string > *obsenum)
{
  bool flag = true;
  set< string > *tmpset = new set< string >;
  if (vars != NULL)
    for (map< string, basictype * >::iterator i = vars->begin();
         i != vars->end(); i++)
      if (i->second->get_type() == 3) {
        set< string > *varset = ((enumerate *) (i->second))->get_enumvalue();
        tmpset->insert(varset->begin(), varset->end());
      }
  if (obsenum != NULL)
    tmpset->insert(obsenum->begin(), obsenum->end());
  if (obsvars != NULL)
    for (map< string, basictype * >::iterator i = obsvars->begin();
         i != obsvars->end(); i++)
      if (tmpset->find(i->first) != tmpset->end()) {
        flag = false;
        cout << "variable " << i->
          first << " has been used as a enumerate value." << endl;
      }
  if (vars != NULL)
    for (map< string, basictype * >::iterator i = vars->begin();
         i != vars->end(); i++)
      if (tmpset->find(i->first) != tmpset->end()) {
        flag = false;
        cout << "variable " << i->
          first << " has been used as a enumerate value." << endl;
      }
  return flag;
}

bool
basic_agent::check_lobsvars(map< string, basictype * >*envars)
{
  if (lobsvars != NULL && lobsvars->size() > 0)
    for (map< string, variable * >::iterator i = lobsvars->begin();
         i != lobsvars->end(); i++) {
      map< string, basictype * >::iterator j;
      if (envars != NULL && (j = envars->find(i->first)) != envars->end())
        i->second->set_var_type(j->second);
      else {
        cout << "local observable variable " << i->
          first << " is not defined in the environment." << endl;
        return false;
      }
    }
  return true;
}

basictype*
basic_agent::get_var_def(string varname) {
	if (obsvars != NULL) {
    map< string, basictype * >::iterator i = obsvars->find(varname);
		if(i != obsvars->end())
			return i->second;
	}
  if (vars != NULL) {
    map< string, basictype * >::iterator i = vars->find(varname);
		if(i != vars->end())
			return i->second;
	}
    
  return NULL;
} 


SddNode*
basic_agent::project_local_state(SddNode * state, SddManager* manager, struct parameters* params)
{
	sdd_ref(state, manager);
  SddNode* tmp = sdd_manager_true(manager); 
	SddNode* gc;
	vector<SddNode*>* v = params->variable_sdds;
  if (lobsvars != NULL && lobsvars->size() > 0) {
    map< string, basictype * >*envars = (*agents)[0]->get_vars();
    for (map< string, basictype * >::iterator i = envars->begin();
         i != envars->end(); i++) {
      if (lobsvars->find(i->first) == lobsvars->end()) {  // i->first is not local observable variable 
        basictype *bt = i->second;
        int index_begin = bt->get_index_begin();
        int index_end = bt->get_index_end();
        for (int j = index_begin; j <= index_end; j++) {
          tmp = sdd_conjoin(gc = tmp, (*v)[j], manager);
					sdd_ref(tmp, manager);
					sdd_deref(gc, manager);
				}
      }
    }
    for (int j = envars_bdd_length; j < get_var_index_begin(); j++) {
      tmp = sdd_conjoin(gc = tmp, (*v)[j], manager);
			sdd_ref(tmp, manager);
			sdd_deref(gc, manager);
    }
  } else {
		for (int j = obsvars_bdd_length; j < get_var_index_begin(); j++) 				{
		    tmp = sdd_conjoin(gc = tmp, (*v)[j], manager);
				sdd_ref(tmp, manager);
				sdd_deref(gc, manager);
		  }
  }
  for (unsigned int j = get_var_index_end() + 1; j < v->size(); j++) {
    tmp = sdd_conjoin(gc = tmp, (*v)[j], manager);
		sdd_ref(tmp, manager);
		sdd_deref(gc, manager);
  }


	// computing state->ExistAbstract(tmp)
	vector<SddLiteral>* literals = new vector<SddLiteral>;
	get_literals(tmp, literals);
	sdd_deref(tmp, manager);
	for(unsigned int k = 0; k < literals->size(); k++) {
		state = sdd_exists((*literals)[k], gc = state, manager);		
		sdd_ref(state, manager);
		sdd_deref(gc, manager);
	}

  return state;

}


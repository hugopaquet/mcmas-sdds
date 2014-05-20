#include <ctime>
#include "types.hh"
#include "utilities.hh"

using namespace std;

assignment::assignment(string * name, expression * value)
{
  var = new variable(name);
  var_value = value;
}

assignment::~assignment()
{
	delete var;
	switch(var_value->get_type()) {
		//case 0: delete (variable *) value; break;
	case 1: delete (bool_value *) var_value; break;
	case 2: delete (int_value *) var_value; break;
	case 3: delete (enum_value *) var_value; break;
	case 5: 
	case 6: 
	case 7: 
	case 8: delete (arithmetic_expression *) var_value; break;
	case 9: 
	case 10: 
	case 11: 
	case 12: delete (bit_expression *) var_value; break;			
	}
}

variable *
assignment::get_var()
{
  return var;
}

expression *
assignment::get_var_value()
{
  return var_value;
}

string
assignment::to_string()
{
  return var->to_string() + " = " + var_value->to_string();
}

bool
assignment::check_var_and_value(map< string, basictype * >*obsvars,
                                map< string, basictype * >*vars)
{
  unsigned char right = var_value->get_type();  // right hand side
  unsigned char right1 = right;
  string vs = var->get_variable_name();
  map< string, basictype * >::iterator p = vars->find(vs);
  if (p == vars->end()) { // the variable is not defined
    cout << "        variable " << vs << " is not defined." << endl;
    return false;
  }
  // add a link in variable to its type
  var->set_var_type(p->second);
  map< string, basictype * >::iterator p1;
  string vs1;
  if (right == 0) {
    vs1 = ((variable *) var_value)->get_variable_name();
    if (((variable *) var_value)->is_agent_name_null()) {
      p1 = vars->find(vs1);
      if (p1 != vars->end()) {  // the variable is a local variable 
        right = p1->second->get_type();
        ((variable *) var_value)->set_var_type(p1->second);
      }
    } else {
      string ag_name = ((variable *) var_value)->get_agent_name();
      if (ag_name == "Environment") {
        p1 = obsvars->find(vs1);
        if (p1 != obsvars->end()) { // the variable is a global variable 
          right = p1->second->get_type();
          ((variable *) var_value)->set_var_type(p1->second);
        }
      }
    }
  } else if (right >= 9 && right <= 12) { // bit_expression
    bool flag =
      ((bit_expression *) var_value)->check_var_and_value(obsvars, vars);
    if (!flag)
      return false;
  }

  unsigned char t1 = p->second->get_type(); //variable's type
  if ((t1 != right && right < 5 && !(t1 == 3 && right == 0)) ||
      (t1 == 3 && right >= 5) || (t1 == 1 && right >= 5 && right <= 8)) {
    cout << "        variable " << vs << " has a wrong typed value." << endl;
    return false;
  }
  if (t1 == 1)      // bool
    return true;
  else if (t1 == 2) {
    if (right1 == 0) {    // rangedint
      int ub = ((rangedint *) (p->second))->get_upperbound();
      int lb = ((rangedint *) (p->second))->get_lowerbound();
      int ub1 = ((rangedint *) (p1->second))->get_upperbound();
      int lb1 = ((rangedint *) (p1->second))->get_lowerbound();
      if (ub < lb1 || ub1 < lb) {
        cout << "        variable " << vs1 <<
          " cannot be assignment to variable " << vs << "." << endl;
        return false;
      } else
        return true;
    } else if (right1 == 2) { // int_value
      if (((rangedint *) (p->second))->
          is_valid_value(((int_value *) var_value)->get_value()))
        return true;
      else {
        cout << "        variable " << vs << " has a wrong integer value." <<
          endl;
        return false;
      }
    } else {      //arithmetic expression
      if (((arithmetic_expression *) var_value)->
          check_var_and_value(obsvars, vars))
        return true;
    }
  } else if (t1 == 3) {   // enum
    if (right == 0) {   // an enum value
      if (((enumerate *) (p->second))->is_valid_value(vs1)) {
        enum_value *tmp = new enum_value(new string(vs1));
        var_value = tmp;  // change it to enum_value
        return true;
      } else {
        cout << "        variable " << vs << " has a wrong enum value '" <<
          vs1 << "'." << endl;
        return false;
      }
    } else {      // an enumerate variable
      set< string > *s1 = ((enumerate *) (p->second))->get_enumvalue();
      set< string > *s2 = ((enumerate *) (p1->second))->get_enumvalue();
      if (s1->size() == s2->size()) { // same size
        bool equal = true;
        for (set< string >::iterator i = s1->begin(); i != s1->end(); i++)
          if (s2->find(*i) == s2->end()) {
            equal = false;
            break;
          }
        if (equal) {
          return true;
        } else {
          cout << "        " << vs << " and " << vs1 <<
            " do not have the same enumerate type." << endl;
          return false;
        }
      } else {
        cout << "        " << vs << " and " << vs1 <<
          " do not have the same enumerate type." << endl;
        return false;
      }
    }
  }
  return false;
}


SddNode*
assignment::encode_sdd(SddManager * manager, struct parameters * params, SddNode* base)
{
  basictype *var_type = var->get_var_type();
  unsigned char value_type = var_type->get_type();
  int begin = var_type->get_index_begin();
  int end = var_type->get_index_end();
  SddNode * encoding = base;
	SddNode* gc;
	sdd_ref(encoding, manager);
  unsigned char var_value_type = var_value->get_type();

  if (value_type == 1) {  // boolean type
    if (var_value_type == 1) {
      if (((bool_value *) var_value)->get_value()) {
				encoding = sdd_conjoin(gc = encoding, (*params->primed_variable_sdds)[begin], manager);
				sdd_ref(encoding, manager);
				sdd_deref(gc, manager);
			}
      else {
				encoding = sdd_conjoin(gc = encoding, sdd_negate((*params->primed_variable_sdds)[begin], manager), manager);	
				sdd_ref(encoding, manager);
				sdd_deref(gc, manager);
			}
    } else if (var_value_type == 0) {
      basictype *var_type1 = ((variable *) var_value)->get_var_type();
      int begin1 = var_type1->get_index_begin();
      // be careful here. rhs is in v and lhs is in pv
			SddNode* node1 = sdd_disjoin(sdd_negate((*params->primed_variable_sdds)[begin], manager),
																		  (*params->variable_sdds)[begin1],	manager);
			sdd_ref(node1, manager);
			SddNode* node2  = sdd_disjoin((*params->primed_variable_sdds)[begin],
																			sdd_negate((*params->variable_sdds)[begin1], manager),
																			manager);
			sdd_ref(node2, manager);
			encoding = sdd_conjoin(gc = encoding, sdd_conjoin(node1, node2, manager), manager);
			sdd_ref(encoding, manager);
			sdd_deref(node1, manager);
			sdd_deref(node2, manager);
			sdd_deref(gc, manager);

    } else {      // bit_operation
      SddNode * rhstrue =
        ((bit_expression *) var_value)->encode_sdd_true(manager,
                                                        params->variable_sdds);
			sdd_ref(rhstrue, manager);
      SddNode * rhsfalse =
        ((bit_expression *) var_value)->encode_sdd_false(manager,
                                                        params->variable_sdds);
			sdd_ref(rhsfalse, manager);
			SddNode* node1 = sdd_negate(sdd_disjoin((*params->primed_variable_sdds)[begin] , rhstrue, manager), manager);
			sdd_ref(node1, manager);
			sdd_deref(rhstrue, manager);
			SddNode* node2 = sdd_disjoin((*params->primed_variable_sdds)[begin], rhsfalse, manager);
			sdd_ref(node2, manager);
			sdd_deref(rhsfalse, manager);
      SddNode * result = sdd_conjoin(node1, node2, manager);
			sdd_ref(result, manager);
			sdd_deref(node1, manager);
			sdd_deref(node2, manager);
      encoding = sdd_conjoin(gc = encoding, result, manager);
			sdd_ref(encoding, manager);
			sdd_deref(gc, manager);
			sdd_deref(result, manager);
    }
  } else if (value_type == 2) { /* // rangedint
    int upperbound = ((rangedint *) var_type)->get_upperbound();
    int lowerbound = ((rangedint *) var_type)->get_lowerbound();

    if (var_value_type == 0) {  // a variable
      basictype *var_type1 = ((variable *) var_value)->get_var_type();
      if (options["quiet"] == 0 && options["verbosity"] > 5) {
        int upperbound1 = ((rangedint *) var_type1)->get_upperbound();
        int lowerbound1 = ((rangedint *) var_type1)->get_lowerbound();
        if (upperbound1 > upperbound) {
          cout << "Warning: \"" << var_value->
            to_string() << "\" might be greater than the upperbound of \"" <<
            var->
            get_variable_name() << "\" in assignment " << to_string() << endl;
        }
        if (lowerbound1 < lowerbound) {
          cout << "Warning: \"" << var_value->
            to_string() << "\"  might be less than the lowerbound of \"" <<
            var->
            get_variable_name() << "\" in assignment " << to_string() << endl;
        }
      }
      ADD rhs =
        ((rangedint *) var_type1)->build_ADD_tree(para->bddmgr, para->addv,
                                                  para->ADD_cache);
      ADD lhs =
        ((rangedint *) var_type)->build_ADD_tree(para->bddmgr, para->addv,
                                                 para->ADD_cache);
      lhs = lhs.SwapVariables(*para->addv, *para->addpv);
      ADD result = addEQ(para->bddmgr, lhs, rhs);
      tmpbdd *= result.BddThreshold(1);
    } else if (var_value_type == 2) { // an integer
      int value = ((int_value *) var_value)->get_value();
      vector< int >*vb = ((rangedint *) var_type)->get_value_index(value);
      for (int i = end; i >= begin; i--)
        if ((*vb)[i - begin] == 1)
          tmpbdd = tmpbdd * (*para->pv)[i];
        else if ((*vb)[i - begin] == -1)
          tmpbdd = tmpbdd * !(*para->pv)[i];
    } else if (var_value_type >= 5 && var_value_type <= 8) {  // arithmetic expression
      ADD rhs =
        ((arithmetic_expression *) var_value)->build_ADD_tree(para->bddmgr,
                                                              para->addv,
                                                              para->
                                                              ADD_cache);
      if (options["quiet"] == 0 && options["verbosity"] > 5) {
        ADD overflow =
          addGT(para->bddmgr, rhs, para->bddmgr->constant(upperbound));
        if (overflow != para->bddmgr->addZero()) {
          cout << "Warning: \"" << var_value->
            to_string() << "\" might be greater than the upperbound of \"" <<
            var->
            get_variable_name() << "\" in assignment " << to_string() << endl;
        }
        ADD underflow =
          addLT(para->bddmgr, rhs, para->bddmgr->constant(lowerbound));
        if (underflow != para->bddmgr->addZero()) {
          cout << "Warning: \"" << var_value->
            to_string() << "\" might be less than the lowerbound of \"" <<
            var->
            get_variable_name() << "\" in assignment " << to_string() << endl;
        }
      }
      ADD lhs =
        ((rangedint *) var_type)->build_ADD_tree(para->bddmgr, para->addv,
                                                 para->ADD_cache);
      lhs = lhs.SwapVariables(*para->addv, *para->addpv);
      ADD result = addEQ(para->bddmgr, lhs, rhs);
      tmpbdd *= result.BddThreshold(1);
    } */
  } else {      // enumerate

		//exit(0);
    if (var_value_type == 3) {
      string value = ((enum_value *) var_value)->get_value();
      vector< bool > *vb = ((enumerate *) var_type)->get_value_index(value);
      for (int i = end; i >= begin; i--)
        if ((*vb)[i - begin])
					encoding = sdd_conjoin(encoding, (*params->primed_variable_sdds)[i], manager);
        else
					encoding = sdd_conjoin(encoding, sdd_negate((*params->primed_variable_sdds)[i], manager), manager);
				sdd_ref(encoding, manager);
    } else {
			cout << "This type of assignment is not supported." << endl;
			exit(0);
   /*   basictype *var_type1 = ((variable *) var_value)->get_var_type();
      ADD rhs =
        ((enumerate *) var_type1)->build_ADD_tree(para->bddmgr, para->addv,
                                                  para->ADD_cache);
      ADD lhs =
        ((enumerate *) var_type)->build_ADD_tree(para->bddmgr, para->addv,
                                                 para->ADD_cache);
      lhs = lhs.SwapVariables(*para->addv, *para->addpv);
      ADD result = addEQ(para->bddmgr, lhs, rhs);
      tmpbdd *= result.BddThreshold(1); */
    } 
  } 
  return encoding;
}


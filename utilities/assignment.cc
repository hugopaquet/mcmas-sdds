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



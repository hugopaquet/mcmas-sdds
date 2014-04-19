#include <ctime>
#include "types.hh"
#include "utilities.hh"

using namespace std;

fairness_expression::fairness_expression(unsigned char o, modal_formula * f1, modal_formula * f2, modal_formula * f3):
  modal_formula(o, f1, f2,
                f3)
{
}

fairness_expression::fairness_expression(unsigned char o, modal_formula * f1,
                                         modal_formula * f2):
  modal_formula(o, f1, f2)
{
}

fairness_expression::fairness_expression(unsigned char o, modal_formula * f1):
  modal_formula(o, f1)
{
}

fairness_expression::fairness_expression(atomic_proposition * obj1):
  modal_formula(obj1)
{
}


SddNode*
fairness_expression::get_sdd_representation()
{
  return sdd_representation;
}

void
fairness_expression::set_sdd_representation(SddNode* sddrep)
{
  sdd_representation = sddrep;
}

void 
fairness_expression::delete_sdd_representation(SddManager* manager)
{
  if(manager != NULL)
    sdd_representation = sdd_manager_false(manager);
}

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


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

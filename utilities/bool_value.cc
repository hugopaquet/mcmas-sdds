#include <ctime>
#include "types.hh"
#include "utilities.hh"

using namespace std;

bool_value::bool_value(bool v):expression(1)
{
  value = v;
}

bool_value::~bool_value()
{
}

bool
bool_value::equal_to(bool_value * expr)
{
  return value == expr->get_value();
}

bool
bool_value::equal_to(expression * expr)
{
  if (expr->get_type() == get_type())
    return equal_to((bool_value *) expr);
  return false;
}

bool
bool_value::get_value()
{
  return value;
}

string
bool_value::to_string()
{
  return (value ? "true" : "false");
}


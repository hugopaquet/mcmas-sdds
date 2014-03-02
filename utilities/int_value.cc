#include <ctime>
#include "types.hh"
#include "utilities.hh"

using namespace std;

int_value::int_value(int v):expression(2)
{
  value = v;
}

int_value::~int_value()
{
}

bool
int_value::equal_to(int_value * expr)
{
  return value == expr->get_value();
}

bool
int_value::equal_to(expression * expr)
{
  if (expr->get_type() == get_type())
    return equal_to((int_value *) expr);
  return false;
}

int
int_value::get_value()
{
  return value;
}

string
int_value::to_string()
{
  ostringstream o;
  o << value;
  return o.str();
}

#include <ctime>
#include "types.hh"
#include "utilities.hh"

using namespace std;

rangedint::rangedint(string * n, int l, int u):basictype(n, 2)
{
  lowerbound = l;
  upperbound = u;
  bdd_length = log_2(upperbound - lowerbound + 1);
  power_two = 1;
  power_two = power_two << bdd_length;
  half_power = 1;
  half_power = half_power << (bdd_length - 1);
  half_power += lowerbound;
}

rangedint::~rangedint()
{
}

int
rangedint::get_lowerbound()
{
  return lowerbound;
}

int
rangedint::get_upperbound()
{
  return upperbound;
}

bool
rangedint::is_valid_value(int i)
{
  return (i <= upperbound && i >= lowerbound);
}

string
rangedint::to_string()
{
  ostringstream o, p;
  o << lowerbound;
  p << upperbound;
  return get_name() + ": " + o.str() + " .. " + p.str();
}

int
rangedint::BDD_length()
{
  return bdd_length;
}

void
rangedint::print_value_index()
{
  for (int k = lowerbound; k <= upperbound; k++) {
    cout << k << ": ";
    vector< int >*v = get_value_index(k);
    for (unsigned int j = 0; j < v->size(); j++)
      cout << ((*v)[j] == 1 ? "1" : ((*v)[j] == -1 ? "0" : "_"));
    cout << endl;
  }
}

vector< int >*
rangedint::get_value_index(int value)
{
  if (value >= lowerbound && value <= upperbound) {
    vector< int >*temp = new vector< int >(bdd_length, -1);
    if (power_two + lowerbound == upperbound + 1) {
      int distance = value - lowerbound;
      for (int i = bdd_length - 1; i >= 0; i--) {
        if ((distance & 1) == 1)
          (*temp)[i] = 1;
        distance >>= 1;
      }
    } else {
      int index = value - half_power;
      if (index < 0) {
        int distance = value - lowerbound;
        for (int i = bdd_length - 2; i >= 0; i--) {
          if ((distance & 1) == 1)
            (*temp)[i] = 1;
          distance >>= 1;
        }
        if (value - lowerbound > upperbound - half_power)
          (*temp)[bdd_length - 1] = 0;
      } else {
        int distance = index;
        for (int i = bdd_length - 2; i >= 0; i--) {
          if ((distance & 1) == 1)
            (*temp)[i] = 1;
          distance >>= 1;
        }
        (*temp)[bdd_length - 1] = 1;
      }
    }
    return temp;
  }
  return NULL;
}

int
rangedint::find_value_by_index(vector< bool > index)
{
  int value = 0;
  if (power_two + lowerbound == upperbound + 1) {
    for (unsigned int i = 0; i < index.size(); i++) {
      value <<= 1;
      value += (index[i] == true ? 1 : 0);
    }
    return value + lowerbound;
  } else {
    for (unsigned int i = 0; i < index.size() - 1; i++) {
      value <<= 1;
      value += (index[i] == true ? 1 : 0);
    }
    if (value > upperbound - half_power || index[bdd_length - 1] == false)
      return value + lowerbound;
    else
      return value + half_power;
  }
}

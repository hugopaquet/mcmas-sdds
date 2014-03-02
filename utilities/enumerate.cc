#include <ctime>
#include "types.hh"
#include "utilities.hh"

using namespace std;

enumerate::enumerate(string * n, set< string > *s):basictype(n, 3)
{
  enumvalue = s;
  value_index = new map< string, vector< bool > *>;
  bdd_length = enumvalue == NULL ? 0 : log_2((int) enumvalue->size());
  set_value_index();
}

enumerate::~enumerate()
{
  delete enumvalue;
	for(map< string, vector< bool > * >::iterator i=value_index->begin(); i!=value_index->end(); i++)
		delete i->second;
	delete value_index;
}

set< string > *enumerate::get_enumvalue()
{
  return enumvalue;
}

int
enumerate::is_valid_value(string s)
{
  if (enumvalue == NULL) {
    cout << "enum list is unknown" << endl;
    exit(1);
  }
  return (enumvalue->find(s) != enumvalue->end());
}

string
enumerate::to_string()
{
  string str = ": { ";
  int k = 0;
  int j = (int) enumvalue->size() - 1;
  for (set< string >::iterator i = enumvalue->begin(); i != enumvalue->end();
       i++) {
    if (k == j)
      str += *i + " ";
    else
      str += *i + ", ";
    k++;
  }
  str += "}";
  return get_name() + str;
}

int
enumerate::BDD_length()
{
  return bdd_length;
}

void
enumerate::set_value_index()
{
  int size = BDD_length();
  vector< bool > base(size, false);
  for (set< string >::iterator i = enumvalue->begin(); i != enumvalue->end();
       i++) {
    vector< bool > *temp = new vector< bool > (base);
    pair < string, vector< bool > *>p(*i, temp);
    value_index->insert(p);
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
enumerate::print_value_index()
{
  for (map< string, vector< bool > *>::iterator i = value_index->begin();
       i != value_index->end(); i++) {
    cout << i->first << ": ";
    for (unsigned int j = 0; j < i->second->size(); j++)
      cout << ((*(i->second))[j] ? 1 : 0);
    cout << endl;
  }
}

vector< bool > *enumerate::get_value_index(string value)
{
  if (value_index != NULL) {
    map< string, vector< bool > *>::iterator i = value_index->find(value);
    if (i != value_index->end())
      return i->second;
  }
  return NULL;
}

string
enumerate::find_value_by_index(vector< bool > index)
{
  for (map< string, vector< bool > *>::iterator i = value_index->begin();
       i != value_index->end(); i++) {
    bool flag = true;
    for (unsigned int j = 0; j < i->second->size(); j++)
      if ((*(i->second))[j] != index[j]) {
        flag = false;
        break;
      }
    if (flag)
      return i->first;
  }
  return "";
}



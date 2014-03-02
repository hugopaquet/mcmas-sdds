#include <ctime>
#include "types.hh"
#include "utilities.hh"

using namespace std;

basictype::basictype(string * n)
{
  name = n;
  type = 1;
  index_begin = -1;
  index_end = -1;
}

basictype::basictype(string * n, unsigned char t)
{
  name = n;
  type = t;
  index_begin = -1;
  index_end = -1;
}

basictype::~basictype()
{
  //delete name;
}

string
basictype::get_name()
{
  if (name == NULL) {
    cout << "type name is unknown" << endl;
    exit(1);
  }
  return *name;
}

unsigned char
basictype::get_type()
{
  return type;
}

string
basictype::to_string()
{
  return *name + ": boolean";
}

int
basictype::BDD_length()
{
  return 1;
}

void
basictype::set_index_begin(int i)
{
  index_begin = i;
  char buff[4];
  sprintf(buff, "%1d", i);
  string str(buff);
  name_index = "_" + *name + "_" + str;
}

void
basictype::set_index_end(int i)
{
  index_end = i;
}

int
basictype::get_index_begin()
{
  return index_begin;
}

int
basictype::get_index_end()
{
  return index_end;
}

void
basictype::print_value_index()
{
  cout << "true: 1" << endl;
  cout << "false: 0" << endl;
}


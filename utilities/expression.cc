#include <ctime>
#include "types.hh"
#include "utilities.hh"

using namespace std;

expression::expression(unsigned char i)
{
  type = i;
}

expression::~expression()
{
}

unsigned char
expression::get_type()
{
  return type;
}

string
expression::to_string()
{
  return "";
}

SddNode* 
expression::encode_sdd_true(SddManager* manager, vector<SddNode*> * v) {
	cout << "Not yet supported: encode_sdd_true() in class expression!" << endl;
	return sdd_manager_true(manager);
}


SddNode* 
expression::encode_sdd_false(SddManager* manager, vector<SddNode*> * v) {
	cout << "Not yet supported: encode_sdd_false() in class expression!" << endl;
	return sdd_manager_false(manager);
}

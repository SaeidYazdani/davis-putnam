/*
 * EDA TOOLS II - Practical Assignement
 * SAT Equivalency Check for digital circuits
 *
 *
 * Name 1: Saeid Yazdani
 * Matriculation Number 1: 394169
 *
 * Name 2: ...
 * Matriculation Number 2: ...
 *
 */

#include <stdio.h>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <map>
#include <string>
#include <cstdlib>

using namespace std;

typedef enum
{
	AND,
	OR,
	INV,
	XOR,
	ZERO,
	ONE,
	UNDEFINED
} GateType;

typedef struct
{
	GateType type;
	vector<int> nets;
} Gate;

typedef vector<Gate> GateList;

int _netCount1, _netCount2;
vector<string> _inputs1, _outputs1, _inputs2, _outputs2;
map<string, int> _map1, _map2;
GateList _gates1, _gates2;
string fileNameA, fileNameB;

int readFile(string filename, int & netCount, vector<string> & inputs, vector<string> & outputs, map<string, int> & map, GateList & gates)
{
	ifstream file(filename.c_str());
	if (! file.is_open())
	{
		return -1;
	}
	string curLine;
	// net count
	getline(file, curLine);
	netCount = atoi(curLine.c_str());
	// inputs
	getline(file, curLine);
	stringstream inputsStream(curLine);
	string buf;
	while (inputsStream >> buf)
	{
		inputs.push_back(buf);
	}
	// outputs
	getline(file, curLine);
	stringstream outputsStream(curLine);
	while (outputsStream >> buf)
	{
		outputs.push_back(buf);
	}
	// mapping
	for (size_t i=0; i<_inputs1.size() + _outputs1.size(); i++)
	{
		getline(file, curLine);
		stringstream mappingStream(curLine);
		mappingStream >> buf;
		int curNet = atoi(buf.c_str());
		mappingStream >> buf;
		map[buf] = curNet;
	}
	// empty line
	getline(file, curLine);
	if (curLine.length() > 1)
	{
		return -1;
	}
	// gates
	while (getline(file, curLine))
	{
		stringstream gateStream(curLine);
		gateStream >> buf;
		Gate curGate;
		curGate.type = (buf == "and" ? AND : buf == "or" ? OR : buf == "inv" ? INV : buf == "xor" ? XOR : buf == "zero" ? ZERO : buf == "one" ? ONE : UNDEFINED);
		if (curGate.type == UNDEFINED)
		{
			return -1;
		}
		while (gateStream >> buf)
		{
			int curNet = atoi(buf.c_str());
			curGate.nets.push_back(curNet);
		}
		gates.push_back(curGate);
	}
	return 0;
}

int readFiles(string filename1, string filename2)
{
	if (readFile(filename1, _netCount1, _inputs1, _outputs1, _map1, _gates1) != 0)
	{
		return -1;
	}
	if (readFile(filename2, _netCount2, _inputs2, _outputs2, _map2, _gates2) != 0)
	{
		return -1;
	}
	return 0;
}

// Prints internal data structure
void printData(int & netCount, vector<string> & inputs, vector<string> & outputs, map<string, int> & map, GateList & gates)
{
	cout << "Net count: " << netCount << "\n\n";
	cout << "Inputs:\n";
	for (size_t i=0; i<inputs.size(); i++)
	{
		cout << inputs[i] << "\n";
	}
	cout << "\n";
	cout << "Outputs:\n";
	for (size_t i=0; i<outputs.size(); i++)
	{
		cout << outputs[i] << "\n";
	}
	cout << "\n";
	cout << "Mapping (input/output port to net number):\n";
	for (size_t i=0; i<inputs.size(); i++)
	{
		cout << inputs[i] << " -> "<< map[inputs[i]] << "\n";
	}
	for (size_t i=0; i<outputs.size(); i++)
	{
		cout << outputs[i] << " -> "<< map[outputs[i]] << "\n";
	}
	cout << "\n";
	cout << "Gates:\n";
	for (size_t i=0; i<gates.size(); i++)
	{
		Gate & curGate = gates[i];
		cout << (curGate.type == AND ? "AND" : curGate.type == OR ? "OR" : curGate.type == INV ? "INV" : curGate.type == XOR ? "XOR" : curGate.type == ZERO ? "ZERO" : curGate.type == ONE ? "ONE" : "ERROR");
		cout << ": ";
		for (size_t j=0; j<curGate.nets.size(); j++)
		{
			cout << curGate.nets[j] << " ";
		}
		cout << "\n";
	}
	cout << "\n";
}

// Prints the internal data structure for netlist 1 or 2
void printDataForNetlist(int netlistNumber)
{
	if (netlistNumber == 1)
	{
		printData(_netCount1, _inputs1, _outputs1, _map1, _gates1);
	}
	else if (netlistNumber == 2)
	{
		printData(_netCount2, _inputs2, _outputs2, _map2, _gates2);
	}
	else
	{
		cout << "Invalid netlist number " << netlistNumber << " (must be 1 or 2)\n";
	}
}


bool empty_clause_check(vector< vector<int> > &cnf)
{
	for(unsigned int i=0; i<cnf.size(); i++)
	{
		vector<int> curClause=cnf[i];
		if (curClause.empty()==true)
		{
			return true;
		}
	}
	return false;
}

void printCNF(vector< vector<int> > & cnf)
{
	for (unsigned int i=0; i<cnf.size(); i++)
	{
		cout << "(";
		vector<int> curClause = cnf[i];
		for (unsigned int j=0; j<curClause.size(); j++)
		{
			cout << curClause[j] << " ";
		}
		cout << ")"<<"\n";
	}
}

void performUnitClauseRule(int counter_examples[], vector<vector<int> >& cnf) {
	// unit clause RULE:
	bool unitClauseFound;
	do {
		unitClauseFound = false;
		for (int i = cnf.size() - 1; i >= 0; i--) {
			if (cnf[i].size() == 1) {
				unitClauseFound = true;
				int temp = cnf[i][0];
				cnf.erase(cnf.begin() + i);
				for (int k = cnf.size() - 1; k >= 0; k--) {
					for (int j = cnf[k].size() - 1; j >= 0; j--) {
						if (cnf[k][j] == -temp) {
							cnf[k].erase(cnf[k].begin() + j);
						} else if (cnf[k][j] == temp) {
							cnf.erase(cnf.begin() + k);
							break;
						}
					}
				}
				if (temp > 0) {
					counter_examples[temp - 1] = 1;
				} else {
					counter_examples[abs(temp) - 1] = 0;
				}
				break;
			}
		}
	} while (unitClauseFound);
}

void solutionFound(int counter_examples[]) {

	cout
	<< "\nCNF is now empty (There are no clauses left)"
	<< "This indicates that a Counter-Example has been found:\n"
	<< endl;

	cout
	<< "INPUT(S):"
	<< endl;


	for (uint i = 0; i < _inputs1.size(); i++) {
		cout
		<< _inputs1[i]
		<< " = "
		<< counter_examples[_map1[_inputs1[i]] - 1]
	    << "\n";
	}

	cout << "" << endl;

	for (uint i = 0; i < _outputs1.size(); i++) {

		cout
		<< "OUTPUT "
		<< _outputs1[i]
		<< " for "
		<< fileNameA
		<< " = "
		<< counter_examples[_map1[_outputs1[i]] - 1]
		<< endl;

		cout
		<< "OUTPUT "
		<< _outputs1[i]
		<< " for "
		<< fileNameB
		<< " = "
		<< counter_examples[_map2[_outputs1[i]] + _netCount1 - 1]
		<< endl;
	}

	//Exit application to stop unfinished recursive calls
	exit(1);
}

int findVariableForBacktracking(vector< vector<int> > &cnf){
	return cnf[cnf.size()-1][cnf[cnf.size()-1].size()-1];
}

void performZeroBacktracking(vector<vector<int> > &cnf0, int currentVariable,
		int counter_examples[]) {

	cout << "Assigning "<< currentVariable << " to 0 \n";
	if (currentVariable >0)
	{
		counter_examples[currentVariable -1]=0;
	}
	else
	{
		counter_examples[abs(currentVariable )-1]=1;
	}

	for (int i = cnf0.size() - 1; i >= 0; i--) {
		vector<int> curClause = cnf0[i];
		for (int j = curClause.size() - 1; j >= 0; j--) {
			if (curClause[j] == -currentVariable) {
				cnf0.erase(cnf0.begin() + i);
				break;
			} else if (curClause[j] == currentVariable) {
				cnf0[i].erase(cnf0[i].begin() + j);
			}
		}
	}
}

void performOneBacktracking(vector<vector<int> > &cnf1, int currentVariable,
		int counter_examples[]) {

	cout << " setting variable "<< currentVariable << "to 1 \n";
	if (currentVariable >0)
	{
		counter_examples[currentVariable -1]=1;
	}
	else
	{
		counter_examples[abs(currentVariable )-1]=0;
	}

	for (int i = cnf1.size() - 1; i >= 0; i--) {
		vector<int> curClause = cnf1[i];
		for (int j = curClause.size() - 1; j >= 0; j--) {
			if (curClause[j] == -currentVariable) {
				cnf1[i].erase(cnf1[i].begin() + j);
			} else if (curClause[j] == currentVariable) {
				cnf1.erase(cnf1.begin() + i);
				break;
			}
		}
	}
}

void DavisPutnam(vector< vector<int> > cnf,int counter_examples[])
{
	//First do unit clause rule
	performUnitClauseRule(counter_examples, cnf);

	//Check for satistifiability conditions
	if(cnf.size()==0) {
		solutionFound(counter_examples);
	} else if(empty_clause_check(cnf)) {
		cout<< "Found an empty clause";
		return;
	} else { //No more heuristics possible, applying backtracking...

		int currentVariable = findVariableForBacktracking(cnf);

		vector< vector<int> > cnf_0 = cnf;
		vector< vector<int> > cnf_1 = cnf;

		//CNF_0
		performZeroBacktracking(cnf_0, currentVariable, counter_examples);
		printCNF(cnf_0);
		DavisPutnam(cnf_0, counter_examples); //recursive call

		//CNF_1
		performOneBacktracking(cnf_1, currentVariable, counter_examples);
		printCNF(cnf_1);
		DavisPutnam(cnf_1,counter_examples); //recursive call
	}
}


uint findHighestNetNumber(vector< vector<int> > &cnf){
	int max = -100000; //this can't go wrong??

	for(uint i = 0; i < cnf.size(); i++) {
		for(uint j = 0; j < cnf[i].size(); j++){
			if(cnf[i][j] > max)
				max = cnf[i][j];
		}
	}

	return abs(max);
}


/* some help for user for how to use the application */
int printHelp(){

	cout
	<< "Invalid arguments or arguments count\n\n"
	<< "Usage:\n"
	<< "\t sat-solver <file1> <file2>\n\n"
	<< "Example:\n"
	<< "\tsat-solver /path/to/file1 /path/to/file2"
	<< endl;

	return -1;
}

void addXorClauses(vector< vector<int> > &cnf, Gate &gate){
	vector<int> cl1,cl2,cl3,cl4;
	cl1.push_back(gate.nets[0]);
	cl1.push_back(gate.nets[1]);
	cl1.push_back(-gate.nets[2]);
	cl2.push_back(-gate.nets[0]);
	cl2.push_back(-gate.nets[1]);
	cl2.push_back(-gate.nets[2]);
	cl3.push_back(-gate.nets[0]);
	cl3.push_back(gate.nets[1]);
	cl3.push_back(gate.nets[2]);
	cl4.push_back(gate.nets[0]);
	cl4.push_back(-gate.nets[1]);
	cl4.push_back(gate.nets[2]);
	cnf.push_back(cl1);
	cnf.push_back(cl2);
	cnf.push_back(cl3);
	cnf.push_back(cl4);
}

void addAndClauses(vector< vector<int> > &cnf, Gate &gate){
	vector<int> cl1,cl2,cl3;
	cl1.push_back(gate.nets[0]);
	cl1.push_back(-gate.nets[2]);
	cl2.push_back(gate.nets[1]);
	cl2.push_back(-gate.nets[2]);
	cl3.push_back(-gate.nets[0]);
	cl3.push_back(-gate.nets[1]);
	cl3.push_back(gate.nets[2]);
	cnf.push_back(cl1);
	cnf.push_back(cl2);
	cnf.push_back(cl3);
}

void addOrClauses(vector< vector<int> > &cnf, Gate &gate){
	vector<int> cl1,cl2,cl3;
	cl1.push_back(-gate.nets[0]);
	cl1.push_back(gate.nets[2]);
	cl2.push_back(-gate.nets[1]);
	cl2.push_back(gate.nets[2]);
	cl3.push_back(gate.nets[0]);
	cl3.push_back(gate.nets[1]);
	cl3.push_back(-gate.nets[2]);
	cnf.push_back(cl1);
	cnf.push_back(cl2);
	cnf.push_back(cl3);
}

void addInvClauses(vector< vector<int> > &cnf, Gate &gate){
	vector<int> cl1,cl2;
	cl1.push_back(gate.nets[0]);
	cl1.push_back(gate.nets[1]);
	cl2.push_back(-gate.nets[0]);
	cl2.push_back(-gate.nets[1]);
	cnf.push_back(cl1);
	cnf.push_back(cl2);
}

void generateMitterInputAndOutputClauses(vector<vector<int> >& cnf) {
	//Generate input miter
	for (size_t i = 0; i < _inputs1.size(); i++) {
		vector<int> cl1, cl2;
		cl1.push_back(-_map1[_inputs1[i]]);
		cl1.push_back(_map2[_inputs1[i]] + _netCount1);
		cl2.push_back(_map1[_inputs1[i]]);
		cl2.push_back(-(_map2[_inputs1[i]] + _netCount1));
		cnf.push_back(cl1);
		cnf.push_back(cl2);
	}
	//Generate output miter
	for (size_t i = 0; i < _outputs1.size(); i++) {
		vector<int> cl1, cl2, cl3, cl4;
		cl1.push_back(_map1[_outputs1[i]]);
		cl1.push_back(_map2[_outputs1[i]] + _netCount1);
		cl1.push_back(-(_netCount1 + _netCount2 + i + 1)); // +1 is important because i starts from 0
		//
		cl2.push_back(-_map1[_outputs1[i]]);
		cl2.push_back(-(_map2[_outputs1[i]] + _netCount1));
		cl2.push_back(-(_netCount1 + _netCount2 + i + 1));
		//
		cl3.push_back(-_map1[_outputs1[i]]);
		cl3.push_back(_map2[_outputs1[i]] + _netCount1);
		cl3.push_back(_netCount1 + _netCount2 + i + 1);
		//
		cl4.push_back(_map1[_outputs1[i]]);
		cl4.push_back(-(_map2[_outputs1[i]] + _netCount1));
		cl4.push_back(_netCount1 + _netCount2 + i + 1);
		cnf.push_back(cl1);
		cnf.push_back(cl2);
		cnf.push_back(cl3);
		cnf.push_back(cl4);
	}
	//complete output miter
	vector<int> cl1;
	for (size_t i = 0; i < _outputs1.size(); i++) {
		cl1.push_back(_netCount1 + _netCount2 + i + 1);
	}
	cnf.push_back(cl1);
}

int main(int argc, char ** argv)
{

	if (argc != 3)
	{
		return printHelp();
	}
	if (readFiles(argv[1], argv[2]) != 0)
	{
		cerr << "Error while reading files!\n";
		return -1;
	}

	fileNameA = argv[1];
	fileNameB = argv[2];

	// The following global variables are now defined (examples are for file xor2.net):
	//
	// int netCount1, netCount2
	// - total number of nets in netlist 1 / 2
	// - e.g. netCount1 is 3
	//
	// vector<string> inputs1, outputs1, inputs2, outputs2
	// - names of inputs / outputs in netlist 1 / 2
	// - e.g. inputs1[0] contains "a_0"
	//
	// map<string, int> map1, map2
	// - mapping from input / output names to net numbers in netlist 1 / 2
	// - e.g. map1["a_0"] is 1, map1["b_0"] is 2, ...
	//
	// GateList gates1, gates2
	// - list (std::vector<Gate>) of all gates in netlist 1 / 2
	// - e.g.:
	//   - gates1[0].type is XOR
	//   - gates1[0].nets is std::vector<int> and contains three ints (one for each XOR port)
	//   - gates1[0].nets[0] is 1 (first XOR input port)
	//   - gates1[0].nets[1] is 2 (second XOR input port)
	//   - gates1[0].nets[2] is 3 (XOR output port)

	// Print out data structure - (for debugging)
	cout << "--------------------------------" << endl;
	cout << "Netlist 1 for '" << fileNameA << "'" << endl;
	cout << "--------------------------------" << endl;
	printDataForNetlist(1);
	cout << "\n--------------------------------" << endl;
	cout << "Netlist 2 for '" << fileNameB << "'" << endl;
	cout << "--------------------------------" << endl;
	printDataForNetlist(2);


	//
	// Add your code to build the CNF.
	// The CNF should be a vector of vectors of ints. Each "inner" vector represents one clause. The "outer" vector represents the whole CNF.
	//
	vector< vector<int> > cnf;

	//Generating CNF clauses for circuit 1
	for (size_t i=0;i < _gates1.size();i++)
	{
		Gate currentGate=_gates1[i];

		switch(currentGate.type){
			case XOR:
				addXorClauses(cnf, currentGate);
				break;

			case AND:
				addAndClauses(cnf, currentGate);
				break;

			case INV:
				addInvClauses(cnf, currentGate);
				break;

			case OR:
				addOrClauses(cnf, currentGate);
				break;

			case ONE:
			case ZERO:
			case UNDEFINED:
					//this shouldent happen!
				break;
		}
	}



	//Generating CNF clauses for circuit 1
	for (size_t i=0;i < _gates2.size();i++)
	{
		//Add offset for second circuti to have unique net numbers
		for(size_t j=0;j< _gates2[i].nets.size();j++)
		{
			_gates2[i].nets[j] += _netCount1;
		}

		Gate currentGate=_gates2[i];

		switch(currentGate.type){
			case XOR:
				addXorClauses(cnf, currentGate);
				break;

			case AND:
				addAndClauses(cnf, currentGate);
				break;

			case INV:
				addInvClauses(cnf, currentGate);
				break;

			case OR:
				addOrClauses(cnf, currentGate);
				break;

			case ONE:
			case ZERO:
			case UNDEFINED:
					//this shouldent happen!
				break;
		}

	}


	//Finalize miter circuit
	generateMitterInputAndOutputClauses(cnf);

	//print newly generated cnf for miter circuit
	printCNF(cnf);


	//set-up for starting Davis-Putnam algorithm
	int counter_examples[findHighestNetNumber(cnf)];

	DavisPutnam(cnf,counter_examples);

	//If for any reason we end up here, it means the circuits are eual
	cout
	<< "\nGiven circuits are equal."
	<< endl;

	//everybody is happy, return 0!
	return 0;
}

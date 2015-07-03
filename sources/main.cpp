/*
 * SAT Equivalence checking for circuit netlists
 *
 *
 * Name 1: Saeid Yazdani
 * Matriculation Number 1: 394169
 */

#include <stdio.h>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <map>
#include <string>
#include <cstdlib>
#include <algorithm>

using namespace std;

typedef enum {
	AND,
	OR,
	INV,
	XOR,
	ZERO,
	ONE,
	UNDEFINED
} GateType;

typedef struct {
	GateType type;
	vector<int> nets;
} Gate;

typedef vector<Gate> GateList;

int netCount1, netCount2;
vector<string> inputs1, outputs1, inputs2, outputs2;
map<string, int> map1, map2;
GateList gates1, gates2;

int readFile(string filename, int & netCount, vector<string> & inputs,
		vector<string> & outputs, map<string, int> & map, GateList & gates) {
	ifstream file(filename.c_str());
	if (! file.is_open())	{
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
	while (inputsStream >> buf)	{
		inputs.push_back(buf);
	}
	// outputs
	getline(file, curLine);
	stringstream outputsStream(curLine);
	while (outputsStream >> buf)	{
		outputs.push_back(buf);
	}
	// mapping
	for (size_t i=0; i<inputs1.size() + outputs1.size(); i++)	{
		getline(file, curLine);
		stringstream mappingStream(curLine);
		mappingStream >> buf;
		int curNet = atoi(buf.c_str());
		mappingStream >> buf;
		map[buf] = curNet;
	}
	// empty line
	getline(file, curLine);
	if (curLine.length() > 1){
		return -1;
	}
	// gates
	while (getline(file, curLine))	{
		stringstream gateStream(curLine);
		gateStream >> buf;
		Gate curGate;
		curGate.type = (buf == "and" ? AND : buf == "or" ? OR
				: buf == "inv" ? INV : buf == "xor" ? XOR
						: buf == "zero" ? ZERO : buf == "one" ? ONE : UNDEFINED);
		if (curGate.type == UNDEFINED){
			return -1;
		}
		while (gateStream >> buf)		{
			int curNet = atoi(buf.c_str());
			curGate.nets.push_back(curNet);
		}
		gates.push_back(curGate);
	}
	return 0;
}

int readFiles(string filename1, string filename2)
{
	if (readFile(filename1, netCount1, inputs1, outputs1, map1, gates1) != 0) {
		return -1;
	}
	if (readFile(filename2, netCount2, inputs2, outputs2, map2, gates2) != 0) {
		return -1;
	}
	return 0;
}

// Prints internal data structure
void printData(int & netCount, vector<string> & inputs
		, vector<string> & outputs, map<string, int> & map, GateList & gates) {
	cout << "Net count: " << netCount << "\n\n";
	cout << "Inputs:\n";
	for (size_t i=0; i<inputs.size(); i++)	{
		cout << inputs[i] << "\n";
	}
	cout << "\n";
	cout << "Outputs:\n";
	for (size_t i=0; i<outputs.size(); i++)	{
		cout << outputs[i] << "\n";
	}
	cout << "\n";
	cout << "Mapping (input/output port to net number):\n";
	for (size_t i=0; i<inputs.size(); i++)	{
		cout << inputs[i] << " -> "<< map[inputs[i]] << "\n";
	}
	for (size_t i=0; i<outputs.size(); i++)	{
		cout << outputs[i] << " -> "<< map[outputs[i]] << "\n";
	}
	cout << "\n";
	cout << "Gates:\n";
	for (size_t i=0; i<gates.size(); i++) {
		Gate & curGate = gates[i];
		cout << (curGate.type == AND ? "AND" : curGate.type == OR ? "OR"
				: curGate.type == INV ? "INV" : curGate.type == XOR ? "XOR"
						: curGate.type == ZERO ? "ZERO"
								: curGate.type == ONE ? "ONE" : "ERROR");
		cout << ": ";
		for (size_t j=0; j<curGate.nets.size(); j++){
			cout << curGate.nets[j] << " ";
		}
		cout << "\n";
	}
	cout << "\n";
}

// Prints the internal data structure for netlist 1 or 2
void printDataForNetlist(int netlistNumber)
{
	if (netlistNumber == 1)	{
		printData(netCount1, inputs1, outputs1, map1, gates1);
	}
	else if (netlistNumber == 2) {
		printData(netCount2, inputs2, outputs2, map2, gates2);
	}
	else {
		cout << "Invalid netlist number "
				<< netlistNumber << " (must be 1 or 2)\n";
	}
}


bool empty_clause_check(vector< vector<int> > cnf)
{
	for(unsigned int i=0; i<cnf.size(); i++) {
		vector<int> curClause=cnf[i];
		if (curClause.empty()==true) {
			return true;
		}
	}
	return false;
}

void printCNF(vector< vector<int> > & cnf)
{
	for (unsigned int i=0; i<cnf.size(); i++) {
		cout << "(";
		vector<int> curClause = cnf[i];
		for (unsigned int j=0; j<curClause.size(); j++)	{
			cout << curClause[j] << " ";
		}
		cout << ")"<<"\n";
	}
}

int findHighestNetNumber(vector<vector<int> >& cnf) {

	int outer= cnf.size()-1;
	int inner=cnf[outer].size()-1;
	return cnf[outer][inner];
}

void performUnitClauseRule(int table_counter_ex[], vector<vector<int> >& cnf) {
	// unit clause RULE:
	bool unitClauseFound;
	do {
		unitClauseFound = false;
		for (int i = cnf.size() - 1; i >= 0; i--) {
			if (cnf[i].size() == 1) {
				unitClauseFound = true;
				int temp = cnf[i][0];
				cnf.erase(cnf.begin() + i);
				for (int j = cnf.size() - 1; j >= 0; j--) {
					for (int k = cnf[j].size() - 1; k >= 0; k--) {
						if (cnf[j][k] == -temp) {
							cnf[j].erase(cnf[j].begin() + k);
						} else if (cnf[j][k] == temp) {
							cnf.erase(cnf.begin() + j);
							break;
						}
					}
				}

				if (temp > 0) {
					table_counter_ex[temp - 1] = 1;
				} else {
					table_counter_ex[abs(temp) - 1] = 0;
				}
				break;
			}
		}
	} while (unitClauseFound);
}

void emptyCnfTermination(int table_counter_ex[]) {
	cout
	<< "CNF Is empty. This is a counter example.\n";
	for (size_t i = 0; i < inputs1.size(); i++) {
		cout << "input: literal number " << inputs1[i] << " => "
				<< table_counter_ex[map1[inputs1[i]] - 1] << "\n";
	}
	for (size_t i = 0; i < outputs1.size(); i++) {
		cout << "output:literal number " << outputs1[i] << " for circuit A"
				<< "=> " << table_counter_ex[map1[outputs1[i]] - 1] << "\n";
		cout << "output:literal number " << outputs1[i] << " for circuit B"
				<< "=> "
				<< table_counter_ex[map2[outputs1[i]] + netCount1 - 1] << "\n";
	}
	exit(1);
}

void performZeroBacktracking(int currentVar, vector<vector<int> >& cnf0
		,int counter_examples[]) {
	cout << " Setting " << currentVar << " to 0 \n";
	if (currentVar > 0)
	{
		counter_examples[currentVar-1]=0;
	}
	else
	{
		counter_examples[abs(currentVar)-1]=1;
	}

	for (int i = cnf0.size() - 1; i >= 0; i--) {
		vector<int> curClause = cnf0[i];
		for (int j = curClause.size() - 1; j >= 0; j--) {
			if (curClause[j] == -currentVar) {
				cnf0.erase(cnf0.begin() + i);
				break;
			} else if (curClause[j] == currentVar) {
				cnf0[i].erase(cnf0[i].begin() + j);
			}
		}
	}
}

void performOneBacktracking(int currentVar, vector<vector<int> >& cnf1
		, int counter_examples[]) {

	cout << " setting variable "<< currentVar<< " to 1 \n";
	if (currentVar>0) {
		counter_examples[currentVar-1]=1;
	}
	else {
		counter_examples[abs(currentVar)-1]=0;
	}


	for (int i = cnf1.size() - 1; i >= 0; i--) {
		vector<int> curClause = cnf1[i];
		for (int j = curClause.size() - 1; j >= 0; j--) {
			if (curClause[j] == -currentVar) {
				cnf1[i].erase(cnf1[i].begin() + j);
			} else if (curClause[j] == currentVar) {
				cnf1.erase(cnf1.begin() + i);
				break;
			}
		}
	}
}

void DavisPutnam(vector< vector<int> > cnf,int counter_examples[]) {

	// unit clause RULE:
	performUnitClauseRule(counter_examples, cnf);

	//Check for satisfiability conditions
	if(cnf.size()==0) { //if cnf does nto contain any clauses
		emptyCnfTermination(counter_examples);
	}
	else if(empty_clause_check(cnf)) {
		cout << "empty clause " << endl;
		return;
	}
	else {
		//No more heuristics possible, doing backtracking

		// finding the most right value
		int currentVar = findHighestNetNumber(cnf);

		vector< vector<int> > cnf_0 = cnf;
		vector< vector<int> > cnf_1 = cnf;


		performOneBacktracking(currentVar, cnf_0 , counter_examples);
		printCNF(cnf_0 );
		DavisPutnam(cnf_0 ,counter_examples);

		performZeroBacktracking(currentVar, cnf_1 , counter_examples);
		printCNF(cnf_1 );
		DavisPutnam(cnf_1 ,counter_examples);
	}

}


void addClausesForXorGate(vector< vector<int> > &cnf, Gate gate){
	vector<int> clause1,clause2,clause3,clause4;
	clause1.push_back(gate.nets[0]);
	clause1.push_back(gate.nets[1]);
	clause1.push_back(-gate.nets[2]);
	clause2.push_back(-gate.nets[0]);
	clause2.push_back(-gate.nets[1]);
	clause2.push_back(-gate.nets[2]);
	clause3.push_back(-gate.nets[0]);
	clause3.push_back(gate.nets[1]);
	clause3.push_back(gate.nets[2]);
	clause4.push_back(gate.nets[0]);
	clause4.push_back(-gate.nets[1]);
	clause4.push_back(gate.nets[2]);
	cnf.push_back(clause1);
	cnf.push_back(clause2);
	cnf.push_back(clause3);
	cnf.push_back(clause4);
}

void addClausesForAndGate(vector< vector<int> > &cnf, Gate gate){
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

void addClausesForOrGate(vector< vector<int> > &cnf, Gate gate){
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

void addClausesForInvGate(vector< vector<int> > &cnf, Gate gate){
	vector<int> cl1,cl2;
	cl1.push_back(gate.nets[0]);
	cl1.push_back(gate.nets[1]);
	cl2.push_back(-gate.nets[0]);
	cl2.push_back(-gate.nets[1]);
	cnf.push_back(cl1);
	cnf.push_back(cl2);
}

void AddMiterInputAndOutputs(vector<vector<int> >& cnf) {
	// Equivalence input stage
	for (size_t i = 0; i < inputs1.size(); i++) {
		vector<int> cl1, cl2;
		cl1.push_back(-map1[inputs1[i]]);
		cl1.push_back(map2[inputs1[i]] + netCount1);
		cl2.push_back(map1[inputs1[i]]);
		cl2.push_back(-(map2[inputs1[i]] + netCount1));
		cnf.push_back(cl1);
		cnf.push_back(cl2);
	}
	//miter for outputs
	for (size_t i = 0; i < outputs1.size(); i++) {
		vector<int> cl1, cl2, cl3, cl4;
		cl1.push_back(map1[outputs1[i]]);
		cl1.push_back(map2[outputs1[i]] + netCount1);
		cl1.push_back(-(netCount1 + netCount2 + i + 1));
		cl2.push_back(-map1[outputs1[i]]);
		cl2.push_back(-(map2[outputs1[i]] + netCount1));
		cl2.push_back(-(netCount1 + netCount2 + i + 1));
		cl3.push_back(-map1[outputs1[i]]);
		cl3.push_back(map2[outputs1[i]] + netCount1);
		cl3.push_back(netCount1 + netCount2 + i + 1);
		cl4.push_back(map1[outputs1[i]]);
		cl4.push_back(-(map2[outputs1[i]] + netCount1));
		cl4.push_back(netCount1 + netCount2 + i + 1);
		cnf.push_back(cl1);
		cnf.push_back(cl2);
		cnf.push_back(cl3);
		cnf.push_back(cl4);
	}
	//or at the end
	vector<int> cl1;
	for (size_t i = 0; i < outputs1.size(); i++) {
		cl1.push_back(netCount1 + netCount2 + i + 1);
	}
	cnf.push_back(cl1);
}

int main(int argc, char ** argv)
{
	if (argc != 3)
	{
		cerr << "Wrong argument count!\n";
		return -1;
	}
	if (readFiles(argv[1], argv[2]) != 0)
	{
		cerr << "Error while reading files!\n";
		return -1;
	}

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
	//   - gates1[0].nets is std::vector<int> and contains three ints
	//     (one for each XOR port)
	//   - gates1[0].nets[0] is 1 (first XOR input port)
	//   - gates1[0].nets[1] is 2 (second XOR input port)
	//   - gates1[0].nets[2] is 3 (XOR output port)

	// Print out data structure - (for debugging)
	cout << "Circuit A:\n==========\n";
	printDataForNetlist(1);
	cout << "\nCircuitt B:\n==========\n";
	printDataForNetlist(2);


	//
	// Add your code to build the CNF.
	// The CNF should be a vector of vectors of ints. Each "inner" vector
	// represents one clause. The "outer" vector represents the whole CNF.
	//
	vector< vector<int> > cnf;

	//********Gates 1*********
	for (size_t i=0;i < gates1.size();i++) {

		Gate currentGate=gates1[i];

		if (currentGate.type == XOR) {
			addClausesForXorGate(cnf, currentGate);
		}

		if (currentGate.type == AND) {
			addClausesForAndGate(cnf, currentGate);
		}

		if (currentGate.type == INV) {
			addClausesForInvGate(cnf, currentGate);
		}

		if (currentGate.type == OR)	{
			addClausesForOrGate(cnf, currentGate);
		}
	}



	//********Gates 2**********
	for (size_t i=0;i < gates2.size();i++) {
		for(size_t j=0;j< gates2[i].nets.size();j++) {
			gates2[i].nets[j] += netCount1;
		}

		Gate currentGate=gates2[i];

		if (currentGate.type == XOR) {
			addClausesForXorGate(cnf, currentGate);
		}

		if (currentGate.type == AND) {
			addClausesForAndGate(cnf, currentGate);
		}

		if (currentGate.type == INV) {
			addClausesForInvGate(cnf, currentGate);
		}

		if (currentGate.type == OR)	{
			addClausesForOrGate(cnf, currentGate);
		}
	}

	//Complete Miter Circuit
	AddMiterInputAndOutputs(cnf);

	printCNF(cnf);

	// finding array size
	int currentVar = findHighestNetNumber(cnf);
	int netNumber = abs(currentVar);
	int counter_examples[netNumber];

	//Enter Davis-Putnam recursive function
	DavisPutnam(cnf,counter_examples);

	//if for any reason we end up here, it means the circuits are equivalent
	cout << "\n  Circuits are equivalent.";

	//return 0 to OS. everybody happy.
	return 0;
}

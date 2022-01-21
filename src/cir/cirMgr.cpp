/****************************************************************************
  FileName     [ cirMgr.cpp ]
  PackageName  [ cir ]
  Synopsis     [ Define cir manager functions ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#include <iostream>
#include <iomanip>
#include <cstdio>
#include <ctype.h>
#include <cassert>
#include <cstring>
#include <algorithm>
#include "cirMgr.h"
#include "cirGate.h"
#include "util.h"
#include "sat.h"
#include "SolverTypes.h"

using namespace std;

// TODO: Implement memeber functions for class CirMgr

/*******************************/
/*   Global variable and enum  */
/*******************************/
CirMgr* cirMgr = 0;
CirGate* CirMgr::Const0 = new CirGate(0, 0, CONST_GATE);


enum CirParseError {
   EXTRA_SPACE,
   MISSING_SPACE,
   ILLEGAL_WSPACE,
   ILLEGAL_NUM,
   ILLEGAL_IDENTIFIER,
   ILLEGAL_SYMBOL_TYPE,
   ILLEGAL_SYMBOL_NAME,
   MISSING_NUM,
   MISSING_IDENTIFIER,
   MISSING_NEWLINE,
   MISSING_DEF,
   CANNOT_INVERTED,
   MAX_LIT_ID,
   REDEF_GATE,
   REDEF_SYMBOLIC_NAME,
   REDEF_CONST,
   NUM_TOO_SMALL,
   NUM_TOO_BIG,

   DUMMY_END
};


/**************************************/
/*   Static varaibles and functions   */
/**************************************/
static unsigned lineNo = 0;  // in printint, lineNo needs to ++
static unsigned colNo  = 0;  // in printing, colNo needs to ++
static char buf[1024];
static string errMsg;
static int errInt;
static CirGate *errGate;

static CirParseError missError;

class Gate
{
public:
   Gate(unsigned i = 0): _gid(i) {}
   ~Gate() {}

   Var getVar() const { return _var; }
   void setVar(const Var& v) { _var = v; }

private:
   unsigned   _gid;  // for debugging purpose...
   Var        _var;
};

static bool
parseError(CirParseError err)
{
   switch (err) {
      case EXTRA_SPACE:
         cerr << "[ERROR] Line " << lineNo+1 << ", Col " << colNo+1
              << ": Extra space character is detected!!" << endl;
         break;
      case MISSING_SPACE:
         cerr << "[ERROR] Line " << lineNo+1 << ", Col " << colNo+1
              << ": Missing space character!!" << endl;
         break;
      case ILLEGAL_WSPACE: // for non-space white space character
         cerr << "[ERROR] Line " << lineNo+1 << ", Col " << colNo+1
              << ": Illegal white space char(" << errInt
              << ") is detected!!" << endl;
         break;
      case ILLEGAL_NUM:
         cerr << "[ERROR] Line " << lineNo+1 << ": Illegal "
              << errMsg << "!!" << endl;
         break;
      case ILLEGAL_IDENTIFIER:
         cerr << "[ERROR] Line " << lineNo+1 << ": Illegal identifier \""
              << errMsg << "\"!!" << endl;
         break;
      case ILLEGAL_SYMBOL_TYPE:
         cerr << "[ERROR] Line " << lineNo+1 << ", Col " << colNo+1
              << ": Illegal symbol type (" << errMsg << ")!!" << endl;
         break;
      case ILLEGAL_SYMBOL_NAME:
         cerr << "[ERROR] Line " << lineNo+1 << ", Col " << colNo+1
              << ": Symbolic name contains un-printable char(" << errInt
              << ")!!" << endl;
         break;
      case MISSING_NUM:
         cerr << "[ERROR] Line " << lineNo+1 << ", Col " << colNo+1
              << ": Missing " << errMsg << "!!" << endl;
         break;
      case MISSING_IDENTIFIER:
         cerr << "[ERROR] Line " << lineNo+1 << ": Missing \""
              << errMsg << "\"!!" << endl;
         break;
      case MISSING_NEWLINE:
         cerr << "[ERROR] Line " << lineNo+1 << ", Col " << colNo+1
              << ": A new line is expected here!!" << endl;
         break;
      case MISSING_DEF:
         cerr << "[ERROR] Line " << lineNo+1 << ": Missing " << errMsg
              << " definition!!" << endl;
         break;
      case CANNOT_INVERTED:
         cerr << "[ERROR] Line " << lineNo+1 << ", Col " << colNo+1 - to_string(errInt).size()
              << ": " << errMsg << " " << errInt << "(" << errInt/2
              << ") cannot be inverted!!" << endl;
         break;
      case MAX_LIT_ID:
         cerr << "[ERROR] Line " << lineNo+1 << ", Col " << colNo+1 - to_string(errInt).size()
              << ": Literal \"" << errInt << "\" exceeds maximum valid ID!!"
              << endl;
         break;
      case REDEF_GATE:
         cerr << "[ERROR] Line " << lineNo+1 << ": Literal \"" << errInt
              << "\" is redefined, previously defined as "
              << errGate->getTypeStr() << " in line " << errGate->getLineNo()
              << "!!" << endl;
         break;
      case REDEF_SYMBOLIC_NAME:
         cerr << "[ERROR] Line " << lineNo+1 << ": Symbolic name for \""
              << errMsg << errInt << "\" is redefined!!" << endl;
         break;
      case REDEF_CONST:
         cerr << "[ERROR] Line " << lineNo+1 << ", Col " << colNo+1 - 1
              << ": Cannot redefine constant (" << errInt << ")!!" << endl;
         break;
      case NUM_TOO_SMALL:
         cerr << "[ERROR] Line " << lineNo+1 << ": " << errMsg
              << " is too small (" << errInt << ")!!" << endl;
         break;
      case NUM_TOO_BIG:
         cerr << "[ERROR] Line " << lineNo+1 << ": " << errMsg
              << " is too big (" << errInt << ")!!" << endl;
         break;
      default: break;
   }
   return false;
}

/**************************************************************/
/*   class CirMgr member functions for circuit construction   */
/**************************************************************/
bool
CirMgr::readCircuit(const string& fileName)
{
   fstream file(fileName.c_str());
   if (!file) { cerr << "Cannot open design \"" << fileName << "\"!!" << endl; return false; }
   
   if (!_readInitial(file)) return false; // will get _type _M _I _L _O _A
   if (!_readPI(file)) return false; // get PIs
   if (!_readPO(file)) return false; // get POs
   if (!_readAIG(file)) return false; // get AIGs
   if (!_readSymb(file)) return false; // read symb
   if (_doComment) {
      char ch;
      while (file.get(ch)) _comment += ch;
   }
   file.close();

   // build connect
   cirMgr->_buildConnect();
   return true;
}

bool CirMgr::_notSpace(char ch) {
   if (isspace(ch)) {
      if (ch == ' ') return parseError(EXTRA_SPACE);
      else { 
         errInt = int(ch);
         return parseError(ILLEGAL_WSPACE);
      }
   }
   return true;
}

bool CirMgr::_beSpace(char ch) {
   if (ch != ' ') return parseError(MISSING_SPACE);
   return true;
}

bool CirMgr::_readNum(string& line, int& num, string err) {
   string numStr = "";
   if (!_notSpace(line[colNo])) return false;
   for (unsigned s = colNo; s < line.size() && !isspace(line[s]); ++s) numStr += line[s];
   if (numStr == "") { errMsg = err; return parseError(missError); }
   for (auto i : numStr) if (!isdigit(i)) {
      errMsg = err +"(" + numStr + ")";
      return parseError(ILLEGAL_NUM);
   }
   num = stoi(numStr);
   colNo += numStr.size();
   return true;
}

bool CirMgr::_readInitial(fstream& file) {
   string line = "";
   getline(file, line);
   if (line.size() == 0) { errMsg = "aag"; return parseError(MISSING_IDENTIFIER); }
   colNo = 0;
   if (!_notSpace(line[0])) return false;
   // check _type
   for (colNo = 0; isalpha(line[colNo]); ++colNo) _type += line[colNo];
   if (_type != "aag") { errMsg = _type; return parseError(ILLEGAL_IDENTIFIER); }
   // check ' M I L O A'
   // read M
   missError = MISSING_NUM;
   if (!_beSpace(line[colNo])) return false;
   colNo += 1;
   if (!_readNum(line, _M, "number of variables")) return false;
   // read I
   if (!_beSpace(line[colNo])) return false;
   colNo += 1;
   if (!_readNum(line, _I, "number of PIs")) return false;
   // read L
   if (!_beSpace(line[colNo])) return false;
   colNo += 1;
   if (!_readNum(line, _L, "number of latches")) return false;
   // read O
   if (!_beSpace(line[colNo])) return false;
   colNo += 1;
   if (!_readNum(line, _O, "number of POs")) return false;
   // read A
   if (!_beSpace(line[colNo])) return false;
   colNo += 1;
   if (!_readNum(line, _A, "number of AIGs")) return false;
   if (colNo < line.size()) return parseError(MISSING_NEWLINE);

   if (_M < _I + _L + _A) {
      errMsg = "Number of variables"; errInt = _M;
      return parseError(NUM_TOO_SMALL);
   }
   if (_L != 0) {
      cerr << "[ERROR] Line 1: Illegal latches!!" << endl;
      return false;
   }

   ++lineNo;
   colNo = 0;
   return true;
}

bool 
CirMgr::_readPI(fstream& file) {
   int repeat = _I;
   missError = MISSING_DEF;
   while (repeat--) {
      int lit;
      string line;
      if (!getline(file, line)) { errMsg = "PI"; return parseError(MISSING_DEF); }
      if (!_readNum(line, lit, "PI")) return false;
      if (colNo < line.size()) return parseError(MISSING_NEWLINE);
      errInt = lit;
      if (lit / 2 == 0) return parseError(REDEF_CONST);
      if (lit % 2) {
         errMsg = "PI";
         return parseError(CANNOT_INVERTED);
      }
      if (lit / 2 > _M) return parseError(MAX_LIT_ID);

      CirPiGate* newPi = new CirPiGate(lit, lineNo + 1);
      for (auto g : _pilist) if (g->getVar() == lit / 2) {
         errGate = g;
         return parseError(REDEF_GATE);
      }
      _pilist.push_back(newPi);
      _gatelist[newPi->getVar()] = newPi;
      ++lineNo;
      colNo = 0;
   }

   return true;
}

bool 
CirMgr::_readPO(fstream& file) {
   missError = MISSING_DEF;
   for (int re = 1; re <= _O; ++re) {
      int lit;
      string line;
      if (!getline(file, line)) { errMsg = "PO"; return parseError(MISSING_DEF); }
      if (!_readNum(line, lit, "PO")) return false;
      if (colNo < line.size()) return parseError(MISSING_NEWLINE);
      errInt = lit;
      if (lit / 2 > _M) return parseError(MAX_LIT_ID);

      CirPoGate* newPo = new CirPoGate(lit, re + _M, lineNo + 1);
      for (auto g : _polist) if (g->getVar() == lit / 2) {
         errGate = g;
         return parseError(REDEF_GATE);
      }
      _polist.push_back(newPo);
      _gatelist[newPo->getVar()] = newPo;
      ++lineNo;
      colNo = 0;
   }

   return true;
}

bool 
CirMgr::_readAIG(fstream& file) {
   int repeat = _A;
   missError = MISSING_DEF;
   while (repeat--) {
      int lit, src1, src2;
      string line;
      if (!getline(file, line)) { errMsg = "AIG"; return parseError(MISSING_DEF); }
      // read AIG lit
      if (!_readNum(line, lit, "AIG")) return false;
      errInt = lit;
      if (lit / 2 == 0) return parseError(REDEF_CONST);
      if (lit % 2) {
         errMsg = "AIG";
         return parseError(CANNOT_INVERTED);
      }
      if (lit / 2 > _M) return parseError(MAX_LIT_ID);

      // read AIG src1
      if (!_beSpace(line[colNo])) return false;
      colNo += 1;
      if (!_readNum(line, src1, "AIG")) return false;
      if (src1 / 2 > _M) { errInt = src1; return parseError(MAX_LIT_ID); }
      // read AIG src2
      if (!_beSpace(line[colNo])) return false;
      colNo += 1;
      if (!_readNum(line, src2, "AIG")) return false;
      if (src2 / 2 > _M) { errInt = src2; return parseError(MAX_LIT_ID); }
      if (colNo < line.size()) return parseError(MISSING_NEWLINE);

      CirAigGate* newAig = new CirAigGate(lit, src1, src2, lineNo + 1);
      for (auto g : _aiglist) if (g->getVar() == lit / 2) {
         errGate = g;
         return parseError(REDEF_GATE);
      }
      for (auto g : _pilist) if (g->getVar() == lit / 2) {
         errGate = g;
         return parseError(REDEF_GATE);
      }
      _aiglist.push_back(newAig);
      _gatelist[newAig->getVar()] = newAig;
      ++lineNo;
      colNo = 0;
   }

   return true;
}

bool CirMgr::_readSymb(fstream& file) {
   string line = "";
   while (getline(file, line)) {
      char type; int pos; string symb;
      if (!_notSpace(line[0])) { return false; }
      type = line[0];
      if (type == 'c') break;
      if (type != 'i' && type != 'l' && type != 'o') {
         errMsg = type; return parseError(ILLEGAL_SYMBOL_TYPE);
      }
      colNo += 1;

      if (!_readNum(line, pos, "symbol index")) return false;
      if (colNo == line.size()) {
         errMsg = "symbolic name";
         return parseError(MISSING_IDENTIFIER);
      }
      
      if (!_beSpace(line[colNo])) { return false; }
      colNo += 1;
      symb = line.substr(colNo);
      if (symb.size() == 0) {
         errMsg = "symbolic name";
         return parseError(MISSING_IDENTIFIER);
      }
      for (size_t i = 0; i < symb.size(); ++i) if (!isprint(symb[i])) {
         errInt = int(symb[i]);
         colNo += i;
         return parseError(ILLEGAL_SYMBOL_NAME);
      }
      switch (type) {
         case 'i':
            if (pos >= _pilist.size()) {
               errMsg = "PI index"; errInt = pos;
               return parseError(NUM_TOO_BIG);
            }
            if (_pilist[pos]->_symbo.size()) {
               errMsg = 'i'; errInt = pos;
               return parseError(REDEF_SYMBOLIC_NAME);
            }
            _pilist[pos]->addSymbol(symb);
            break;
         case 'o':
            if (pos >= _polist.size()) {
               errMsg = "PO index"; errInt = pos;
               return parseError(NUM_TOO_BIG);
            }
            if (_polist[pos]->_symbo.size()) {
               errMsg = 'o'; errInt = pos;
               return parseError(REDEF_SYMBOLIC_NAME);
            }
            _polist[pos]->addSymbol(symb);
            break;
         default:
            return false;
      }
      ++lineNo;
      colNo = 0;
   }
   // get "c" or nothing
   if (line.size()) {
       colNo += 1;
       if (colNo != line.size()) return parseError(MISSING_NEWLINE);
       _doComment = true;
   }
   return true;
}
/**********************************************************/
/*   class CirMgr member functions for circuit printing   */
/**********************************************************/
/*********************
Circuit Statistics
==================
  PI          20
  PO          12
  AIG        130
------------------
  Total      162
*********************/
void
CirMgr::printSummary() const
{
   cout << endl;
   cout << "Circuit Statistics" << endl;
   cout << "==================" << endl;
   cout << "  PI" << right << setw(12) << _pilist.size() << endl;
   cout << "  PO" << right << setw(12) << _polist.size() << endl;
   cout << "  AIG" << right << setw(11) << _aiglist.size() << endl;
   cout << "------------------" << endl;
   cout << "  Total" << right << setw(9) << _pilist.size() + _polist.size() + _aiglist.size() << endl;
}

void
CirMgr::printNetlist() const
{
   cout << endl;
   for (size_t i = 0;i < _dfslist.size(); ++i) {
      CirGate* g = _dfslist[i];
      cout << "[" << i << "] ";
      cout << left << setw(4) << g->getTypeStr() << g->_var;
      for (size_t j = 0;j < g->_fanin.size(); ++j) {
         cout << " " << (g->_fanin[j]->_gateType == UNDEF_GATE ? "*" : "") \
            << (g->_inv[j] ? "!" : "") << g->_fanin[j]->_var;
      }
      if (g->_symbo != "") cout << " (" << g->_symbo << ")";
      cout << endl;
   }
}

void
CirMgr::printPIs() const
{
   cout << "PIs of the circuit:";
   for (size_t i = 0;i < _pilist.size(); ++i) 
      cout << " " << _pilist[i]->getVar();
   cout << endl;
}

void
CirMgr::printPOs() const
{
   cout << "POs of the circuit:";
   for (size_t i = 0;i < _polist.size(); ++i) 
      cout << " " << _polist[i]->getVar();
   cout << endl;
}

void
CirMgr::printFloatGates() const
{
   vector<unsigned> fltFanins;
   vector<unsigned> notUsed;
   for (map<unsigned, CirGate*>::const_iterator it = _gatelist.begin(); it != _gatelist.end(); ++it) {
      CirGate* gate = it->second;
      if (gate->getType() == CONST_GATE || gate->getType() == UNDEF_GATE) continue;
      for (auto i : gate->_fanin) {
         if (i->getType() == UNDEF_GATE) {
            fltFanins.push_back(gate->getVar());
            break;
         }
      }

      if ((gate->_fanout).empty() && gate->getType() != PO_GATE) notUsed.push_back(gate->getVar());
   }

   if (!fltFanins.empty()) {
      cout << "Gates with floating fanin(s):";
      for (size_t i = 0;i < fltFanins.size(); ++i)
         cout << " " << fltFanins[i];
      cout << endl;
   }
   if (!notUsed.empty()) {
      cout << "Gates defined but not used  :";
      for (size_t i = 0;i < notUsed.size(); ++i)
         cout << " " << notUsed[i];
      cout << endl;
   }
}

void
CirMgr::writeAag(ostream& outfile) const
{
   outfile << _type << " " << _M << " " << _I << " " \
      << _L << " " << _O << " ";
   // count AIG in _dfslist
   int validA = 0;
   for (auto i : _dfslist) if (i->_gateType == AIG_GATE) ++validA;
   outfile << validA << endl;

   for (auto i : _pilist) outfile << i->_var * 2 << endl;
   for (auto i : _polist) {
      outfile << i->_fanin[0]->_var * 2 + int(i->_inv[0]) << endl;
   }
   for (auto i : _dfslist) {
      if (i->_gateType == AIG_GATE) {
         outfile << i->_var * 2;
         for (size_t j = 0;j < i->_fanin.size(); ++j) {
            outfile << " " << i->_fanin[j]->_var * 2 + int(i->_inv[j]);
         }
         outfile << endl;
      }
   }
   for (size_t i = 0;i < _pilist.size(); ++i) {
      if (_pilist[i]->_symbo.size()) outfile << "i" << i << " " << _pilist[i]->_symbo << endl;
   }
   for (size_t i = 0;i < _polist.size(); ++i) {
      if (_polist[i]->_symbo.size()) outfile << "o" << i << " " << _polist[i]->_symbo << endl;
   }
   string myComment = "AAG output by Che-Kuang (Ken) Chu";
   outfile << "c\n" << myComment << endl;
}


void
CirMgr::_buildConnect() {
   _gatelist[0] = Const0;
   for (map<unsigned, CirGate*>::iterator it = _gatelist.begin(); it != _gatelist.end(); ++it) {
      if (it->second->_gateType == PO_GATE || it->second->_gateType == AIG_GATE) it->second->connect(_gatelist);
   }
   genDFSList();
}

void
CirMgr::genDFSList() {
   CirGate::setGlobalRef();
   for (size_t i = 0;i < _polist.size(); ++i) _dfs(_polist[i]);
}

void
CirMgr::_dfs(CirGate* gate) {
   gate->setToGlobalRef();
   for (size_t i = 0;i < gate->_fanin.size(); ++i) {
      if (!gate->_fanin[i]->isGlobalRef()) {
         _dfs(gate->_fanin[i]);
      }
   }
   if (gate->_gateType != UNDEF_GATE) _dfslist.push_back(gate);
}

void
CirMgr::reset() {
   _pilist.clear();
   _polist.clear();
   _aiglist.clear();
   _dfslist.clear();
   for (map<unsigned, CirGate*>::iterator it = _gatelist.begin(); it != _gatelist.end(); ++it) {
      delete it->second;
   }
   _gatelist.clear();
   CirMgr::Const0 = new CirGate(0, 0, CONST_GATE);

   _M = _I = _L = _O = _A = 0;
   _doComment = 0;
   _comment = _type = "";

   lineNo = 0;
   colNo = 0;
}

void
CirMgr::satRARAlg() {
   bool isPO = false;
   SatSolver solver;
   solver.initialize();
   reverse(_dfslist.begin(), _dfslist.end());

   int counter = 0;
   int w = 0;
   int g = 0;

   _genProofModel(solver);
   vector<unsigned> dominID;
   vector<vector<unsigned>> dominIDs(_M + _O, dominID);
   GateList dominators;
   vector<GateList> dominGates(_M + _O, dominators);
   unsigned int recordHead;
   unsigned int recordTail;

   for (size_t i = 0; i < _dfslist.size(); ++i) {
      // no need to consider PO
      if (_dfslist[i]->getTypeStr() != "AIG") {
         continue;
      }

      short *times = new short[_M+_O]();
      _addDominator(_dfslist[i], times);
      for (size_t j = 0; j < _dfslist.size(); ++j) {
         if (_dfslist[j]->getTypeStr() == "AIG") {
            if (times[_dfslist[j]->getVar() - 1] == _dfslist[i]->_fanout.size()) {
               dominGates.at(_dfslist[i]->getVar()-1).push_back(_dfslist[j]);
               dominIDs.at(_dfslist[i]->getVar()-1).push_back(_dfslist[j]->getVar());
            }
         }
      }
      reverse(dominGates.at(_dfslist[i]->getVar()-1).begin(), dominGates.at(_dfslist[i]->getVar()-1).end());
      reverse(dominIDs.at(_dfslist[i]->getVar()-1).begin(), dominIDs.at(_dfslist[i]->getVar()-1).end());

      delete [] times;

      // no need to consider gate which connect to PO
      for (size_t j = 0; j < _dfslist[i]->_fanout.size(); ++j) {
         if (_dfslist[i]->_fanout[j]->getTypeStr() == "PO")
            isPO = true;
      }

      if (isPO) {
         isPO = false;
         continue;
      }
      else {
         for (size_t j = 0; j < _dfslist[i]->_fanout.size(); ++j) {
            ++counter;
            if(recordHead == _dfslist[i]->getVar() && recordTail == _dfslist[i]->_fanout[j]->getVar()) {
               cout << "FUCK this gate: " << _dfslist[i]->getVar() << " & its fanout : " << _dfslist[i]->_fanout[j]->getVar() << endl;
               continue;
            }
            Wire wt(_dfslist[i], _dfslist[i]->_fanout[j]);
            solver.assumeRelease();
            recordHead = _dfslist[i]->getVar();
            recordTail = _dfslist[i]->_fanout[j]->getVar();
            _satRAR(wt, solver, w, g, dominIDs, dominGates);
            cout << "\ntotal alternative wires :\t" << w << "\ntotal alternative gates :\t" << g << endl;
         }
      }  
   }
   cout << "\n#tar : " << counter << "\n#alt wire : " << w << "\n#alt gate : " << g << endl;
}

void
CirMgr::_satRAR(Wire& tarWire, SatSolver& solver, int& ws, int& gs, vector<vector<unsigned>> dominIDs, vector<GateList> dominGates) {
   cout << "\ntarget wire : " << tarWire.first->_var << "-" << tarWire.second->_var << endl;
   
   MA MA_wt;
   vector<unsigned> inputID;
   bool wt_result;

   for (size_t i = 1; i <= _dfslist.size(); ++i) {
      MA_wt.insert({i, 2});
   }
   MA MA_tmp = MA_wt;
   
   solver.assumeRelease();
   solver.assumeProperty(tarWire.first->getVar(), true);

   wt_result = solver.MASolve(MA_wt, dominIDs[tarWire.first->getVar()-1]);

   // Propogation of wt's MA 
   inputID.push_back(tarWire.first->getVar());
   if (dominIDs[tarWire.first->getVar()-1].size() >= 1) {
      inputID.insert(inputID.end(), dominIDs[tarWire.first->getVar()-1].begin(), dominIDs[tarWire.first->getVar()-1].end()-1);
   }

   Wire pt = tarWire;
   solver.assumeRelease();
   for (size_t i = 0; i < dominIDs[tarWire.first->getVar()-1].size(); ++i) {
      if (i != 0) {
         pt = Wire(dominGates[tarWire.first->getVar()-1][i-1], dominGates[tarWire.first->getVar()-1][i]);
      }

      int flag = (pt.second->_fanin[0] != pt.first) ? 0 : 1;
         
      solver.assumeProperty(pt.second->_fanin[flag]->getVar(), pt.second->_inv[flag] ? false : true);
      wt_result = solver.MASolveTwo(MA_wt, dominIDs[tarWire.first->getVar()-1], inputID);
      if (!wt_result) {
         cout << "Oh, no~~ There is a conflict in MA of wt..." << endl;
         return;
      }
   }
   

   // Excitation of wt's MA 

   solver.resetAssign();

   // MAs of every gd
   MAList MA_domin;
   vector<vector<unsigned>> fanoutIDs;
   
   for (size_t i = 0; i < dominIDs[tarWire.first->getVar()-1].size(); ++i) {
      MA MA_now = MA_tmp;
      vector<unsigned> fID;
      vector<unsigned> iID;

      bool gd_result;
      // find fanout cone of each dominator
      _addFanoutCone(dominGates[tarWire.first->getVar()-1][i], fID);
      fanoutIDs.push_back(fID);
      fID.clear();
      
      // find MA of each dominator
      solver.assumeRelease();
      solver.assumeProperty(dominIDs[tarWire.first->getVar()-1][i], true);
      gd_result = solver.MASolve(MA_now, dominIDs[dominIDs[tarWire.first->getVar()-1][i]-1]);

      iID.push_back(dominIDs[tarWire.first->getVar()-1][i]);
      if (dominIDs[dominIDs[tarWire.first->getVar()-1][i]-1].size() >= 1) {
         iID.insert(iID.end(), dominIDs[dominIDs[tarWire.first->getVar()-1][i]-1].begin(), dominIDs[dominIDs[tarWire.first->getVar()-1][i]-1].end()-1);
      }


      solver.assumeRelease();
      for (size_t k = 0; k < dominIDs[dominIDs[tarWire.first->getVar()-1][i]-1].size(); ++k) {
         if (k != 0) {
            pt = Wire(dominGates[dominIDs[tarWire.first->getVar()-1][i]-1][k-1], dominGates[dominIDs[tarWire.first->getVar()-1][i]-1][k]);
         } else {
            pt = Wire(dominGates[tarWire.first->getVar()-1][i], dominGates[dominIDs[tarWire.first->getVar()-1][i]-1][0]);
         }
         int flag = (pt.second->_fanin[0] != pt.first) ? 0 : 1;
         solver.assumeProperty(pt.second->_fanin[flag]->getVar(), pt.second->_inv[flag] ? false : true);
         gd_result = solver.MASolveTwo(MA_now, dominIDs[dominIDs[tarWire.first->getVar()-1][i]-1], iID);
         if (!gd_result) {
            cout << "Oh, no~~ There is a conflict in MA of gd..." << endl;
            return;
         }
      }
      iID.clear();

      for (size_t j = 1; j <= _dfslist.size(); ++j) {
         // if input gate of the target wire has not been assign value and has conflict
         if (j != tarWire.first->_var && MA_wt[j] != 2 && MA_now[j] != 2 && MA_wt[j] != MA_now[j]) {
            cout << j << " : " << MA_wt[j] << " " << MA_now[j] << endl;
            cout << "Oh, no~~ There is a conflict..." << endl;
            return;
         }
      }

      MA_domin.push_back(MA_now);  

      solver.resetAssign();
   }

   // find alternative wires
   vector<vector<unsigned>> wires;
   bool result = true;
   MA MA_check;
   MA tmp;
   for (size_t i = 0; i < MA_domin.size(); ++i) {
      // Do not select gate in fanout cone of dominator
      tmp = MA_wt;
      for (size_t j = 0; j < fanoutIDs[i].size(); ++j) {
         tmp.erase(fanoutIDs[i][j]);
      }

      for (MA::iterator it = tmp.begin(); it != tmp.end(); ++it) {
        
         if (it->first == tarWire.first->_var && dominIDs[tarWire.first->getVar()-1][i] == tarWire.second->_var) continue;
         
         if (MA_domin[i][it->first] == 2 && it->second != 2) {
            solver.assumeRelease();
            for (MA::iterator it2 = MA_domin[i].begin(); it2 != MA_domin[i].end(); ++it2) {
               if (it2->second != 2) {
                  solver.assumeProperty(it2->first, it2->second);
               }
            }
            solver.assumeProperty(it->first, it->second);
            result = solver.ConflictSolve(dominIDs[dominIDs[tarWire.first->getVar()-1][i]]);
            if (!result) {
               wires.push_back({it->first, dominIDs[tarWire.first->getVar()-1][i]});
               ws++;
            }

            solver.resetAssign();
            result = true;
         }

         else if (MA_domin[i][it->first] != 2 && it->second != 2 && MA_domin[i][it->first] != it->second) {
            wires.push_back({it->first, dominIDs[tarWire.first->getVar()-1][i]});
            ws++;
         }
      }
   }
   
   // print out alternative wires
   // cout << '\n' << "alternative wires: " << wires.size() << '\n';
   // for (size_t i = 0; i < wires.size(); ++i) {
   //    cout << wires[i][0] << ' ' << wires[i][1] << endl;
   // }

   vector<vector<unsigned>> gateAlt;
   for (size_t i = 0; i < MA_domin.size(); ++i) {
      // Do not select gate in fanout cone of dominator
      tmp = MA_wt;
      for (size_t j = 0; j < fanoutIDs[i].size(); ++j) {
         tmp.erase(fanoutIDs[i][j]);
      }
      for (MA::iterator it = tmp.begin(); it != tmp.end(); ++it) {
         if (MA_domin[i][it->first] == 2 && it->second != 2) {
            solver.assumeRelease();
            for (MA::iterator it2 = MA_domin[i].begin(); it2 != MA_domin[i].end(); ++it2) {
               if (it2->second != 2) {
                  solver.assumeProperty(it2->first, it2->second);
               }
            }
         
            MA_check = MA_domin[i];
            solver.assumeProperty(it->first, it->second);
            MA_check[it->first] = it->second;
            result = solver.MASolve(MA_check, dominIDs[dominIDs[tarWire.first->getVar()-1][i]-1]);
            if (!result) {
               continue;
            }

            for (MA::iterator it2 = MA_check.begin(); it2 != MA_check.end(); ++it2) {
               if (it2->second != 2) {
                  if (MA_wt[it2->first] != 2 && MA_wt[it2->first] != it2->second) {
                     vector<unsigned> tmpp = {it2->first, it->first, dominIDs[tarWire.first->getVar()-1][i]};
                     if (find(gateAlt.begin(), gateAlt.end(), tmpp) == gateAlt.end()) {
                        gateAlt.push_back({it->first, it2->first, dominIDs[tarWire.first->getVar()-1][i]});
                        gs++;
                     }
                  }
               }
            }

            solver.resetAssign();
            result = true;
         }
      }
   }

   // print out alternative gates
   // cout << '\n' << "alternative gates: " << gateAlt.size() << '\n';
   // for (size_t i = 0; i < gateAlt.size(); ++i) {
   //    cout << gateAlt[i][0] << " & " << gateAlt[i][1] << "->" << gateAlt[i][2] << endl;
   // }
   
   fanoutIDs.clear();
   MA_domin.clear();
   wires.clear();
   gateAlt.clear();
}

void
CirMgr::_addDominator(CirGate* tarGate, short *& times) {
   for (size_t i = 0; i < tarGate->_fanout.size(); ++i) {
      if(tarGate->_fanout[i]->getTypeStr()=="PO") return;
      else {
         times[tarGate->_fanout[i]->_var - 1] ++;
         _addDominator(tarGate->_fanout[i], times);
      }
   }
}

void
CirMgr::_addFanoutCone(CirGate* tarGate, vector<unsigned>& fanoutID) {
   if(tarGate->getTypeStr()=="PO") return;

   for (size_t i = 0; i < tarGate->_fanout.size(); ++i) {
      fanoutID.push_back(tarGate->_fanout[i]->_var);
      _addFanoutCone(tarGate->_fanout[i], fanoutID);
   }
}

void
CirMgr::_genProofModel(SatSolver& s) {
   vector<Gate *> gates;
   
   for (size_t i = 1; i <= _dfslist.size(); ++i) {
      gates.push_back(new Gate(i));
      Var v = s.newVar();
      gates[i-1]->setVar(v);
   }

   for (size_t i = 0; i < _dfslist.size(); ++i) {
      cout << "gate ID: " << _dfslist[i]->getVar() << "\tgate type: " << _dfslist[i]->getTypeStr() << "\tfanin size: " << _dfslist[i]->_fanin.size() << "\tfanout size: " << _dfslist[i]->_fanout.size() << endl;
      if (_dfslist[i]->getTypeStr() == "PI" && _dfslist[i]->getTypeStr() == "PO") {
         continue;
      }
      else if (_dfslist[i]->getTypeStr() == "AIG") {
         s.addAigCNF(gates[_dfslist[i]->_var-1]->getVar(), gates[_dfslist[i]->_fanin[0]->_var-1]->getVar(), _dfslist[i]->_inv[0],
                     gates[_dfslist[i]->_fanin[1]->_var-1]->getVar(), _dfslist[i]->_inv[1]);
      }
   }
}
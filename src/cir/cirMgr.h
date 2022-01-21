/****************************************************************************
  FileName     [ cirMgr.h ]
  PackageName  [ cir ]
  Synopsis     [ Define circuit manager ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef CIR_MGR_H
#define CIR_MGR_H

#include <vector>
#include <string>
#include <fstream>
#include <iostream>
#include <map>

using namespace std;

#include "cirGate.h"
#include "cirDef.h"
#include "sat.h"

extern CirMgr *cirMgr;

// TODO: Define your own data members and member functions
class CirMgr
{
public:
  CirMgr(): _M(0), _I(0), _L(0), _O(0), _A(0), _doComment(0), _comment(""), _type("") {}
  ~CirMgr() { reset(); }

  // Access functions
  // return '0' if "gid" corresponds to an undefined gate.
  CirGate* getGate(unsigned gid) const {
    if (_gatelist.find(gid) == _gatelist.end()) return 0;
    return _gatelist.find(gid)->second;
  }

  // Member functions about circuit construction
  bool readCircuit(const string&);

  // Member functions about circuit reporting
  void printSummary() const;
  void printNetlist() const;
  void printPIs() const;
  void printPOs() const;
  void printFloatGates() const;
  void writeAag(ostream&) const;

  // Member functions about circuit DFS
  void genDFSList();

  // CONST 0 gate
  static CirGate* Const0;

  // reseting
  void reset();

  // satRAR
  void satRARAlg();

private:
  // for parsing
  bool _readInitial(fstream&);
  bool _readPI(fstream&);
  bool _readPO(fstream&);
  bool _readAIG(fstream&);
  bool _readSymb(fstream&);

  bool _notSpace(char);
  bool _beSpace(char);
  bool _readNum(string&, int&, string);

  void _buildConnect();
  void _dfs(CirGate*);
  
  void _satRAR(Wire&, SatSolver&, int&, int&, vector<vector<unsigned>>, vector<GateList>);
  void _addDominator(CirGate*, short *&);
  void _addFanoutCone(CirGate*, vector<unsigned>&);
  void _genProofModel(SatSolver&);

  bool _doComment;
  string _comment;
  string _type;

  int _M, _I, _L, _O, _A;
  vector<CirPiGate*> _pilist;
  vector<CirPoGate*> _polist;
  vector<CirAigGate*> _aiglist;
  vector<CirGate*> _dfslist;
  map<unsigned, CirGate*> _gatelist;
};

#endif // CIR_MGR_H

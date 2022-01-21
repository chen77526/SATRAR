/****************************************************************************
  FileName     [ cirGate.h ]
  PackageName  [ cir ]
  Synopsis     [ Define basic gate data structures ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef CIR_GATE_H
#define CIR_GATE_H

#include <string>
#include <vector>
#include <iostream>
#include "cirDef.h"

using namespace std;

class CirMgr;
class CirGate;
class CirPiGate;
class CirPoGate;
class CirAigGate;

//------------------------------------------------------------------------
//   Define classes
//------------------------------------------------------------------------
// TODO: Define your own data members and member functions, or classes
class CirGate
{
public:
  CirGate() {}
  CirGate(int var, int lineNo, GateType gateType): _var(var), _lineNo(lineNo), _gateType(gateType) {}
  virtual ~CirGate() { reset(); }

  friend class CirMgr;

  // Basic access methods
  string getTypeStr() const {
    switch(_gateType) {
      case UNDEF_GATE: return "UNDEF";
      case PI_GATE: return "PI";
      case PO_GATE: return "PO";
      case AIG_GATE: return "AIG";
      case CONST_GATE: return "CONST";
      case TOT_GATE: return "TOT_GATE";
      default: return "";
    }
  }
  unsigned getLineNo() const { return _lineNo; }

  // Printing functions
  // virtual void printGate() const = 0;
  void printGate() {} // this is I add
  void reportGate() const;
  void reportFanin(int level);
  void reportFanout(int level);

  unsigned getVar() { return _var; }
  GateType getType() { return _gateType; }

  void connect(map<unsigned, CirGate*>&);

  void addSymbol(const string& symb) {
    _symbo = symb;
  }

  bool isGlobalRef() { return _ref == _globalRef; }
  void setToGlobalRef() { _ref = _globalRef; }
  static void setGlobalRef() { ++_globalRef; }

  void reset();

private:
  static unsigned _globalRef;
  unsigned _ref;

  void _dfsFanin(CirGate*, unsigned, bool, int);
  void _dfsFanout(CirGate*, unsigned, bool, int);

protected:
  GateType _gateType;
  unsigned _var;
  unsigned _lineNo;
  vector<CirGate*> _fanin;
  vector<CirGate*> _fanout;
  vector<bool> _inv; // input inverse
  vector<bool> _outv; // output inverse
  string _symbo;
};

class CirPiGate : public CirGate
{
public:
  CirPiGate() {}
  CirPiGate(int lit, unsigned lineNo) {
    _gateType = PI_GATE;
    _lineNo = lineNo;
    _var = lit / 2;
    _symbo = "";
  }
  ~CirPiGate() { reset(); }
};

class CirPoGate : public CirGate
{
public:
  CirPoGate() {}
  CirPoGate(int srclit, int var, unsigned lineNo) {
    _gateType = PO_GATE;
    _lineNo = lineNo;
    _var = var;

    _inv.push_back(srclit % 2 == 1 ? 1 : 0);

    size_t srcVar = (size_t)(srclit / 2);
    _fanin.push_back((CirGate*)srcVar);
    _symbo = "";
  }
  ~CirPoGate() { reset(); }
};

class CirAigGate : public CirGate
{
public:
  CirAigGate() {}
  CirAigGate(int lit, int src1, int src2, unsigned lineNo) {
    _gateType = AIG_GATE;
    _lineNo = lineNo;
    _var = lit / 2;

    _inv.push_back(src1 % 2 == 1 ? 1 : 0);
    _inv.push_back(src2 % 2 == 1 ? 1 : 0);

    size_t var1 = (size_t)(src1 / 2);
    size_t var2 = (size_t)(src2 / 2);
    _fanin.push_back((CirGate*)var1);
    _fanin.push_back((CirGate*)var2);
    _symbo = "";
  }
  ~CirAigGate() { reset(); }
};

#endif // CIR_GATE_H

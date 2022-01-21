/****************************************************************************
  FileName     [ cirGate.cpp ]
  PackageName  [ cir ]
  Synopsis     [ Define class CirAigGate member functions ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#include <iostream>
#include <iomanip>
#include <sstream>
#include <stdarg.h>
#include <cassert>
#include <map>
#include "cirGate.h"
#include "cirMgr.h"
#include "util.h"

using namespace std;

extern CirMgr *cirMgr;

// TODO: Implement memeber functions for class(es) in cirGate.h

/**************************************/
/*   class CirGate member functions   */
/**************************************/
unsigned CirGate::_globalRef = 0;

void
CirGate::reportGate() const
{
   cout << "==================================================" << endl;
   string s = "= " + getTypeStr() + "(" + to_string(_var) + ")" \
      + (_symbo == "" ? "" : "\"" + _symbo + "\"") + ", line " + to_string(_lineNo);
   cout << s << right << setw(50 - s.size()) << "=" << endl;
   cout << "==================================================" << endl;
}

void
CirGate::reportFanin(int level)
{
   assert (level >= 0);
   setGlobalRef();
   _dfsFanin(this, 0, 0, level);
}

void
CirGate::_dfsFanin(CirGate* g, unsigned spaces, bool inv, int level) {
   for (size_t i = 0; i < spaces; ++i) cout << " ";
   if (inv) cout << "!";
   cout << g->getTypeStr() << " " << g->_var;
   // check if need to add (*)
   if (g->isGlobalRef() && level > 0 && !g->_fanin.empty()) {
      cout << " (*)" << endl; return;
   }
   else cout << endl;
   // dfs next level
   if (level == 0) return;
   g->setToGlobalRef();
   for (size_t i = 0; i < g->_fanin.size(); ++i) {
      _dfsFanin(g->_fanin[i], spaces + 2, g->_inv[i], level - 1);
   }
}

void
CirGate::reportFanout(int level)
{
   assert (level >= 0);
   setGlobalRef();
   _dfsFanout(this, 0, 0, level);
}

void
CirGate::_dfsFanout(CirGate* g, unsigned spaces, bool inv, int level) {
   for (size_t i = 0; i < spaces; ++i) cout << " ";
   if (inv) cout << "!";
   cout << g->getTypeStr() << " " << g->_var;
   // check if need to add (*)
   if (g->isGlobalRef() && level > 0 && !g->_fanout.empty()) {
      cout << " (*)" << endl; return;
   }
   else cout << endl;
   // dfs next level
   if (level == 0) return;
   g->setToGlobalRef();
   for (size_t i = 0; i < g->_fanout.size(); ++i) {
      _dfsFanout(g->_fanout[i], spaces + 2, g->_outv[i], level - 1);
   }
}

 void 
 CirGate::connect(map<unsigned, CirGate*>& gatelist) {
    for (size_t i = 0;i < _fanin.size(); ++i) {
      size_t inVar = (size_t)(void*)_fanin[i];
       if (gatelist.find(inVar) == gatelist.end()) {
          CirGate* floatGate = new CirGate(inVar, 0, UNDEF_GATE);
          gatelist[inVar] = floatGate;
       }
      // set _fanin and _fanout
      _fanin[i] = gatelist[inVar];
      _fanin[i]->_fanout.push_back(this);
      _fanin[i]->_outv.push_back(_inv[i]);
    }
 }

 void
 CirGate::reset() {
    _fanin.clear();
    _fanout.clear();
    _inv.clear();
    _outv.clear();
 }

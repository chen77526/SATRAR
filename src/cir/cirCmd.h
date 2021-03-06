/****************************************************************************
  FileName     [ cirCmd.h ]
  PackageName  [ cir ]
  Synopsis     [ Define basic cir package commands ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef CIR_CMD_H
#define CIR_CMD_H

#include "cmdParser.h"

CmdClass(CirReadCmd);
CmdClass(CirPrintCmd);
CmdClass(CirGateCmd);
CmdClass(CirWriteCmd);
CmdClass(CirSatRARCmd);

#endif // CIR_CMD_H

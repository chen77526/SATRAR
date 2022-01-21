cirGate.o: cirGate.cpp cirGate.h cirDef.h cirMgr.h ../../include/sat.h \
 ../../include/Solver.h ../../include/SolverTypes.h \
 ../../include/Global.h ../../include/VarOrder.h ../../include/Heap.h \
 ../../include/Proof.h ../../include/File.h ../../include/util.h \
 ../../include/rnGen.h ../../include/myUsage.h
cirMgr.o: cirMgr.cpp cirMgr.h cirGate.h cirDef.h ../../include/sat.h \
 ../../include/Solver.h ../../include/SolverTypes.h \
 ../../include/Global.h ../../include/VarOrder.h ../../include/Heap.h \
 ../../include/Proof.h ../../include/File.h ../../include/util.h \
 ../../include/rnGen.h ../../include/myUsage.h \
 ../../include/SolverTypes.h
cirCmd.o: cirCmd.cpp cirMgr.h cirGate.h cirDef.h ../../include/sat.h \
 ../../include/Solver.h ../../include/SolverTypes.h \
 ../../include/Global.h ../../include/VarOrder.h ../../include/Heap.h \
 ../../include/Proof.h ../../include/File.h cirCmd.h \
 ../../include/cmdParser.h ../../include/cmdCharDef.h \
 ../../include/util.h ../../include/rnGen.h ../../include/myUsage.h

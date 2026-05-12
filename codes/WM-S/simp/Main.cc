/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007,      Niklas Sorensson

Copyright (c) 2017, Mao Luo, Chu-Min LI, Fan Xiao: implementing a learnt clause
minimisation approach Reference: M. Luo, C.-M. Li, F. Xiao, F. Manya, and Z. L.
, “An effective learnt clause minimization approach for cdcl sat solvers,” in
IJCAI-2017, 2017, pp.703-711.

Maple_CM, Based on Maple_LCM --Copyright (c) 2018, Chu-Min LI, Mao Luo, Fan
Xiao: implementing a clause minimisation approach.


Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>
#include <signal.h>
#include <sys/resource.h>
#include <zlib.h>

#include <iostream>

#include "core/Dimacs.h"
#include "core/PrintFlags.h"
#include "simp/BLO.h"
#include "simp/SimpSolver.h"
#include "utils/Options.h"
#include "utils/ParseUtils.h"
#include "utils/System.h"

using namespace Minisat;
using namespace std;

static Solver* kBaseSolver;
// Terminate by notifying the solver and back out gracefully. This is mainly to
// have a test-case for this feature of the Solver as it may take longer than an
// immediate call to '_exit()'.
// static void SIGINT_interrupt(int signum) { kBaseSolver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that
// 'exit()' calls destructors and may cause deadlocks if a malloc/free function
// happens to be running (these functions are guarded by locks for multithreaded
// use).
static void SIGINT_exit(int signum) {
  printf("\n");
  printf("c *** INTERRUPTED ***\n");
  printf("s UNKNOWN\n");
  if (kBaseSolver->verbosity > 0) {
    printf("c ===================================================\n");
    kBaseSolver->printSummaryStat();
    printf("\n");
    printf("c *** INTERRUPTED ***\n");
  }

  _exit(1);
}

void initialSolver(SimpSolver& solver, bool pre, int verb, bool drup = false,
                   const char* drup_file = nullptr,
                   WeightType user_init_ub = INT64_MAX,
                   WeightType user_init_lb = 0) {
  // Set some solver options:
  kBaseSolver = &solver;
  if (!pre) {
    solver.eliminate(true);
  }

  solver.parsing = true;
  solver.verbosity = verb;
  if (drup && strlen(drup_file)) {
    solver.drup_file = strlen(drup_file) ? fopen(drup_file, "wb") : stdout;
    if (solver.drup_file == NULL) {
      solver.drup_file = stdout;
      printf("c Error opening %s for write.\n", (const char*)drup_file);
    }
    printf("c DRUP proof generation: %s\n",
           solver.drup_file == stdout ? "stdout" : drup_file);
  }

  solver.initUB = user_init_ub;
  solver.initLB = user_init_lb;
  printf("c initial UB: %" PRId64 "\n", solver.initUB);
  printf("c initial LB: %" PRId64 "\n", solver.initLB);

  if (solver.initUB < INT64_MAX) {
    solver.initUB--;
  }
}

enum ResultType { UNKNOWN = 0, UNSAT = 2, OPTIMUM = 3 };

void parseInstance(SimpSolver& solver, Parser<SimpSolver>* parser) {
  double initial_time = cpuTime();

  if (!parser->isOK()) {
    printf("c ERROR! Could not open input file.\n");
    printf("s UNKNOWN\n");
    exit(1);
  }

  parser->parse_DIMACS();
  parser->closeFile();

  // Print statistics of the original instance:
  if (solver.verbosity > 0) {
    printf("c ================[ Problem Statistics]==================\n");
  }

  if (solver.verbosity > 0) {
    printf("c Number of variables:  %12d\n", solver.nVars());
    printf("c Number of clauses:    %12d\n", solver.nClauses());
  }

  double parsed_time = cpuTime();
  if (solver.verbosity > 0) {
    printf("c Parse time:           %12.2f s\n", parsed_time - initial_time);
  }
}

ResultType simpleSolve(SimpSolver& solver) {
  double parsed_time = cpuTime();
  // Perform simplification:
  solver.parsing = false;
  solver.setFrozenVars();
  solver.eliminate(true);
  double simplified_time = cpuTime();
  if (solver.verbosity > 0) {
    printf("c Simplification time:  %12.2f s\n\n",
           simplified_time - parsed_time);
  }

  if (!solver.okay()) {
    // Instance is solved during simplification:
    if (solver.verbosity > 0) {
      printf("c======================================================\n");
      printf("c Solved by simplification\n");
      solver.printSummaryStat();
      printf("\n");
    }
    return UNSAT;
  }

  // Search for a model by calling the solver:
  vec<Lit> dummy;
  lbool ret = solver.solveLimited(dummy);
  if (solver.verbosity > 0) {
    solver.printSummaryStat();
    printf("\n");
  }
  if (ret == l_False) {
    if (solver.initUB < INT64_MAX) {
      printf(
          "c Could not improve the input UB. UB-1 is proved unsatisfiable\n");
    }
    return UNSAT;
  } else if (solver.feasible && ret == l_True) {
    return OPTIMUM;
  }

  return UNKNOWN;
}

SimpSolver* createSolverInstance() {
  SimpSolver* solver = new SimpSolver();
  if (solver == NULL) {
    printf("c ERROR! Could not create solver object.\n");
    exit(1);
  }
  return solver;
}

SimpSolver* checkOrCreateBLOInstance(SimpSolver* solver, const char* inst_file,
                                     bool pre, int verb, bool drup,
                                     const char* drup_file,
                                     WeightType user_init_ub,
                                     WeightType user_init_lb) {
  vec<WeightType> blo_weights;
  if (solver->isBLOInstance(blo_weights)) {
    printf("c Detected instance is a BLO instance.\n");
    vec<WeightType> harden_weights;
    WeightType blo_harden_ub = user_init_ub;
    // Try to harden from the largest weight to the second smallest weight.
    for (int i = blo_weights.size() - 1; i > 0; i--) {
      WeightType current_weight = blo_weights[i];
      printf("c Try to harden weight %" PRId64 "\n", current_weight);
      harden_weights.push(current_weight);
      delete solver;
      solver = createSolverInstance();
      initialSolver(*solver, pre, verb, drup, drup_file, current_weight);
      BLOParser<SimpSolver> blo_parser(*solver, inst_file, harden_weights,
                                       true);
      parseInstance(*solver, &blo_parser);
      ResultType result = simpleSolve(*solver);
      if (result == UNSAT) {
        printf("c UNSAT after hardening weight %" PRId64 "\n", current_weight);
        harden_weights.pop();  // Remove the last testing weight.
        break;
      } else if (result == OPTIMUM) {
        printf("c Successfully hardened weight %" PRId64 "\n", current_weight);
        if (current_weight < blo_harden_ub) {
          blo_harden_ub = current_weight;
        }
      } else {
        printf("c UNKNOWN after hardening weight %" PRId64 "\n",
               current_weight);
        printf("s UNKNOWN\n");
        exit(1);
      }
    }
    // Recreate the solver with all the hardened weights.
    delete solver;
    solver = createSolverInstance();
    initialSolver(*solver, pre, verb, drup, drup_file, blo_harden_ub,
                  user_init_lb);

    BLOParser<SimpSolver> blo_parser(*solver, inst_file, harden_weights);
    parseInstance(*solver, &blo_parser);
  }
  return solver;
}

void printResults(SimpSolver& solver, ResultType result) {
  if (result == OPTIMUM) {
    printf("s OPTIMUM FOUND\n");
    printf("v ");
#ifdef printFinalSolution
    for (int i = 0; i < solver.nbOriginalVars; i++) {
      printf(solver.model[i] == l_True ? "1" : "0");
    }
#endif
    printf("\n");
  } else if (result == UNSAT) {
    printf("s UNSATISFIABLE\n");
  } else {
    printf("s UNKNOWN\n");
  }

  if (solver.drup_file && result == UNSAT) {
#ifdef BIN_DRUP
    solver.binDRUP_flush(solver.drup_file);
    fputc('a', solver.drup_file);
    fputc(0, solver.drup_file);
#else
    fprintf(solver.drup_file, "0\n");
#endif
  }
  if (solver.drup_file && solver.drup_file != stdout) {
    fclose(solver.drup_file);
  }
}

int getReturnCode(ResultType result) {
  if (result == OPTIMUM)
    return 30;
  else if (result == UNSAT)
    return 20;
  else if (result == UNKNOWN)
    return 10;
  else
    return 0;
}

void setResourceLimit(IntOption cpu_lim, IntOption mem_lim) {
  // Use signal handlers that forcibly quit until the solver will be able to
  // respond to interrupts:
  signal(SIGINT, SIGINT_exit);
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGABRT, SIGINT_exit);

  // Set limit on CPU-time:
  if (cpu_lim != INT32_MAX) {
    rlimit rl;
    getrlimit(RLIMIT_CPU, &rl);
    if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max) {
      rl.rlim_cur = cpu_lim;
      if (setrlimit(RLIMIT_CPU, &rl) == -1)
        printf("c WARNING! Could not set resource limit: CPU-time.\n");
    }
  }

  // Set limit on virtual memory:
  if (mem_lim != INT32_MAX) {
    rlim_t new_mem_lim = (rlim_t)mem_lim * 1024 * 1024;
    rlimit rl;
    getrlimit(RLIMIT_AS, &rl);
    if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max) {
      rl.rlim_cur = new_mem_lim;
      if (setrlimit(RLIMIT_AS, &rl) == -1)
        printf("c WARNING! Could not set resource limit: Virtual memory.\n");
    }
  }
}

//=================================================================================================
// Main:

int main(int argc, char** argv) {
  try {
    setUsageHelp(
        "USAGE: %s [options] <input-file> \n\n  where input may be either in "
        "plain or gzipped DIMACS.\n");

#if defined(__linux__)
    fpu_control_t oldcw, newcw;
    _FPU_GETCW(oldcw);
    newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE;
    _FPU_SETCW(newcw);
    printf(
        "c WARNING: for repeatability, setting FPU to use double "
        "precision\n");
#endif

    // Extra options:
    IntOption verb("MAIN", "verb",
                   "Verbosity level (0=silent, 1=some, 2=more).", 1,
                   IntRange(0, 2));
    BoolOption pre("MAIN", "pre", "Completely turn on/off any preprocessing.",
                   true);
    IntOption cpu_lim("MAIN", "cpu-lim",
                      "Limit on CPU time allowed in seconds.\n", INT32_MAX,
                      IntRange(0, INT32_MAX));
    IntOption mem_lim("MAIN", "mem-lim",
                      "Limit on memory usage in megabytes.\n", INT32_MAX,
                      IntRange(0, INT32_MAX));
    Int64Option user_init_ub("MAIN", "init-ub", "The initial upper bound.\n",
                             INT64_MAX, Int64Range(0, INT64_MAX));
    Int64Option user_init_lb("MAIN", "init-lb", "The initial lower bound.\n", 0,
                             Int64Range(0, INT64_MAX));
    BoolOption drup("MAIN", "drup", "Generate DRUP UNSAT proof.", false);
    StringOption drup_file("MAIN", "drup-file", "DRUP UNSAT proof ouput file.",
                           "");

    parseOptions(argc, argv, true);

    // The only left argument should be the input file:
    if (argc == 1) {
      printUsageAndExit(argc, argv, false);
    }
    const char* inst_file = argv[1];
    setResourceLimit(cpu_lim, mem_lim);

    SimpSolver* solver = createSolverInstance();
    initialSolver(*solver, pre, verb, drup, drup_file, user_init_ub,
                  user_init_lb);
    Parser<SimpSolver> parser(*solver, inst_file);
    parseInstance(*solver, &parser);
    solver = checkOrCreateBLOInstance(solver, inst_file, pre, verb, drup,
                                      drup_file, user_init_ub, user_init_lb);

    ResultType result = simpleSolve(*solver);
    printResults(*solver, result);

#ifndef NDEBUG
    // Check the model:
    if (result == OPTIMUM) {
      gzFile myin = gzopen(inst_file, "rb");
      check_solution_DIMACS(myin, *solver);
    }
#endif

#ifdef NDEBUG
    // exit is faster than "return", which will invoke the destructor functions.
    exit(getReturnCode(result));
#else
    if (solver != NULL) {
      delete solver;
    }
    return getReturnCode(result);
#endif
  } catch (OutOfMemoryException&) {
    printf("c ===============================================\n");
    printf("c Out of memory\n");
    printf("s UNKNOWN\n");
    exit(0);
  }
}

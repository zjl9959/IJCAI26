#ifndef MAXCDCL_ISET_H
#define MAXCDCL_ISET_H
#include "Solver.h"
#include "core/SolverTypes.h"
#include "mtl/Vec.h"

namespace Minisat {

struct Iset {
  vec<Lit> lits;
  int64_t weight;
  Iset() : lits(), weight(0) {};
  void reset() {
    lits.clear();
    weight = 0;
  }
};

}  // namespace Minisat
#endif
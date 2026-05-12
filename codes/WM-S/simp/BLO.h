#ifndef Minisat_BLO_H
#define Minisat_BLO_H

#include <stdio.h>

#include "core/Dimacs.h"
#include "core/SolverTypes.h"
#include "utils/ParseUtils.h"

namespace Minisat {

template <class Solver>
class BLOParser : public Parser<Solver> {
 protected:
  bool skip_soft_;                   // Discard soft clauses when parsing.
  vec<WeightType>& harden_weights_;  // Weights of soft clauses to be hardened.
  int max_var_id_ = INT32_MIN;

 public:
  BLOParser(Solver& solver, const char* inst_file,
            vec<WeightType>& harden_weights, bool skip_soft = false)
      : Parser<Solver>(solver, inst_file),
        skip_soft_(skip_soft),
        harden_weights_(harden_weights) {}
  ~BLOParser() {}

 protected:
  virtual void onParseVar(int var) override {
    if (var > max_var_id_) max_var_id_ = var;
  }

  virtual void onParseHardClause(vec<Lit>& lits, int64_t weight) override {
    createVarsInSolver();
    this->solver_.addClause_(lits, weight);
  }

  virtual void onParseSoftClause(vec<Lit>& lits, int64_t weight) override {
    if (harden_weights_.find(weight) != -1) {
      // Harden the soft clause if its weight is in the harden_weights_ map.
      createVarsInSolver();
      this->solver_.addClause_(lits, weight);
    } else if (!skip_soft_) {
      // Only add the soft clause if we want to solve the instance as
      createVarsInSolver();
      this->solver_.addClause_(lits, weight);
      this->solver_.totalWeight += weight;
    }
  }

 private:
  void createVarsInSolver() {
    while (max_var_id_ >= this->solver_.nVars()) {
      this->solver_.newVar();
    }
    max_var_id_ = INT32_MIN;
  }
};

}  // namespace Minisat

#endif  // Minisat_BLO_H

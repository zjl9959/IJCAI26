/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <stdio.h>

#include "core/SolverTypes.h"
#include "utils/ParseUtils.h"

namespace Minisat {

//=================================================================================================
// DIMACS Parser:

template <class Solver>
class Parser {
 protected:
  Solver& solver_;
  gzFile in_raw_;
  StreamBuffer in_;
  int inst_type_ = -1;  // -1: unknown; 0: cnf; 1: wcnf

 public:
  Parser(Solver& s, const char* inst_file)
      : solver_(s), in_raw_(NULL), in_(in_raw_) {
    in_raw_ = gzopen(inst_file, "rb");
    if (in_raw_ != NULL) {
      in_ = StreamBuffer(in_raw_);
    }
  }
  ~Parser() { closeFile(); }

  inline bool isOK() const { return in_raw_ != NULL; }

  inline bool isEof() const { return *in_ == EOF; }

  inline void closeFile() {
    if (in_raw_ != NULL) {
      gzclose(in_raw_);
      in_raw_ = NULL;
    }
  }

  // Inserts problem into solver.
  void parse_DIMACS() {
    if (!isOK() || isEof()) return;
    for (;;) {
      skipWhitespace(in_);
      if (isEof())
        break;
      else if (*in_ == 'p') {
        parse_DIMACS_old();
        break;
      } else if (*in_ == 'h' || *in_ == '-' || (*in_ >= '0' && *in_ <= '9')) {
        parse_DIMACS_new();
        break;
      } else if (*in_ == 'c')
        skipLine(in_);
    }
  }

 protected:
  virtual void onParseMetaData(WeightType hardWeight) {
    solver_.hardWeight = hardWeight;
    solver_.instanceType = inst_type_;
    if (hardWeight > 0) solver_.UB = hardWeight;
    solver_.totalWeight = 0;
  }

  virtual void onFinishedParsing() {
    solver_.nbOriVars = solver_.nVars();
    solver_.nbOriginalVars = solver_.nVars();
  }

  virtual void onParseVar(int var) {
    while (var >= solver_.nVars()) {
      solver_.newVar();
    }
  }

  virtual void onParseHardClause(vec<Lit>& lits, int64_t weight) {
    solver_.addClause_(lits, weight);
  }

  virtual void onParseSoftClause(vec<Lit>& lits, int64_t weight) {
    solver_.addClause_(lits, weight);
    solver_.totalWeight += weight;
  }

 private:
  void readClause(vec<Lit>& lits, int64_t& weight) {
    int parsed_lit, var;
    lits.clear();
    if (inst_type_ != 0)
      weight = parseUint64(in_);
    else
      weight = 1;
    for (;;) {
      parsed_lit = parseInt(in_);
      if (parsed_lit == 0) break;
      var = abs(parsed_lit) - 1;
      onParseVar(var);
      lits.push((parsed_lit > 0) ? mkLit(var) : ~mkLit(var));
    }
  }

  void readClause_new(vec<Lit>& lits) {
    int parsed_lit, var;
    lits.clear();
    for (;;) {
      parsed_lit = parseInt(in_);
      if (parsed_lit == 0) break;
      var = abs(parsed_lit) - 1;
      onParseVar(var);
      lits.push((parsed_lit > 0) ? mkLit(var) : ~mkLit(var));
    }
  }

  void parse_DIMACS_old() {
    vec<Lit> lits;
    int cnt = 0;
    int nbVars = 0;
    int clauses = 0;
    WeightType hardWeight = 0;

    assert(*in_ == 'p');
    if (eagerMatch(in_, "p cnf")) {
      nbVars = parseInt(in_);
      clauses = parseInt(in_);
      inst_type_ = 0;
      onParseMetaData(hardWeight);
    } else if (eagerMatch(in_, "wcnf")) {
      nbVars = parseInt(in_);
      clauses = parseInt(in_);
      inst_type_ = 1;
      while (*in_ == 32) ++in_;
      if (*in_ != '\n') {
        hardWeight = parseUint64(in_);
      }
      onParseMetaData(hardWeight);
    } else {
      printf("PARSE ERROR! Unexpected char: %c\n", *in_), exit(3);
    }

    for (;;) {
      skipWhitespace(in_);
      if (*in_ == EOF)
        break;
      else if (*in_ == 'p') {
      } else if (*in_ == 'c' || *in_ == 'p')
        skipLine(in_);
      else {
        cnt++;
        int64_t weight;
        readClause(lits, weight);
        assert(weight > 0);
        if (hardWeight == 0 || weight < hardWeight) {
          onParseSoftClause(lits, weight);
        } else {
          onParseHardClause(lits, weight);
        }
      }
    }
    if (nbVars != solver_.nVars())
      fprintf(stderr,
              "WARNING! DIMACS header mismatch: wrong number of variables.\n");
    if (cnt != clauses)
      fprintf(stderr,
              "WARNING! DIMACS header mismatch: wrong number of clauses.\n");
  }

  // Format post-2022
  // Line p wcnf x y z is not present
  // Hard clauses start with h
  void parse_DIMACS_new() {
    vec<Lit> lits;
    WeightType hardWeight = INT64_MAX;
    inst_type_ = 1;
    onParseMetaData(hardWeight);

    for (;;) {
      skipWhitespace(in_);
      if (*in_ == EOF)
        break;
      else if (*in_ == 'c')
        skipLine(in_);
      else {
        int64_t weight;
        bool is_soft_clause = false;
        if (*in_ == 'h') {
          weight = INT64_MAX;
          ++in_;
          skipWhitespace(in_);
        } else {
          weight = parseUint64(in_);
          is_soft_clause = true;
        }
        readClause_new(lits);
        assert(weight > 0);
        if (is_soft_clause)
          onParseSoftClause(lits, weight);
        else
          onParseHardClause(lits, weight);
      }
    }
    onFinishedParsing();
  }
};

//=================================================================================================
template <class B, class Solver>
static void check_solution_DIMACS_main(B& in, Solver& S) {
  int vars = 0;
  int clauses = 0;
  int cnt = 0, unsatcnt = 0;
  int64_t cost = 0;
  bool newFormat = true;
  S.hardWeight = INT64_MAX;
  S.instanceType = 1;
  for (;;) {
    skipWhitespace(in);
    if (*in == EOF)
      break;
    else if (*in == 'p') {
      if (eagerMatch(in, "p cnf")) {
        vars = parseInt(in);
        clauses = parseInt(in);
        S.hardWeight = 0;
        S.instanceType = 0;
        newFormat = false;
      } else if (eagerMatch(in, "wcnf")) {
        vars = parseInt(in);
        clauses = parseInt(in);
        while (*in == 32) ++in;
        if (*in == '\n')
          S.hardWeight = 0;
        else
          S.hardWeight = parseInt(in);
        S.instanceType = 1;
        newFormat = false;
      } else {
        printf("c PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
      }
    } else if (*in == 'c' || *in == 'p')
      skipLine(in);
    else {
      cnt++;
      int parsed_lit, var;
      bool ok = false;
      int64_t weight;
      vec<Lit> lits;
      if (S.instanceType != 0) {
        skipWhitespace(in);
        if (newFormat && *in == 'h') {
          weight = S.hardWeight;
          ++in;
        } else
          weight = parseUint64(in);
      } else
        weight = 1;
      lits.clear();
      for (;;) {
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit) - 1;
        lits.push((parsed_lit > 0) ? mkLit(var) : ~mkLit(var));
        if ((parsed_lit > 0 && S.model[var] == l_True) ||
            (parsed_lit < 0 && S.model[var] == l_False))
          ok = true;
      }
      if (!ok) {
        if (S.instanceType == 0)
          cost += weight;
        else if (S.hardWeight > 0 && weight >= S.hardWeight) {
          printf("c hard clause %d is not satisfied\n", cnt);
          unsatcnt++;
          for (int i = 0; i < lits.size(); i++) printf("%d ", toInt(lits[i]));
          printf("\n");
          break;
        } else
          cost += weight;
      }
    }
  }
  if (!newFormat && cnt != clauses)
    printf(
        "c WARNING! DIMACS header mismatch: wrong number of clauses. %d %d "
        "%d\n",
        cnt, clauses, vars);
  else if (unsatcnt == 0) {
    if (cost == S.optimal)
      printf(
          "c solution checked against the original DIMACS file with correct "
          "cost %" PRId64 " over the total cost %" PRId64 "\n",
          cost, S.totalWeight);
    else {
      printf(
          "c solution checked against the original DIMACS file with wrong "
          "cost\n");
      printf("c real cost : %" PRId64 ", solution cost : %" PRId64 "\n", cost,
             S.solutionCost);
      assert(cost == S.optimal);
    }
  } else {
    printf("c solution infeasible with %d unsat hard clauses\n", unsatcnt);
    assert(unsatcnt == 0);
  }
}

template <class Solver>
static void check_solution_DIMACS(gzFile input_stream, Solver& S) {
  StreamBuffer in(input_stream);
  check_solution_DIMACS_main(in, S);
}

}  // namespace Minisat

#endif

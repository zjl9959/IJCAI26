/****************************************************************************************[Solver.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
        Copyright (c) 2007-2010, Niklas Sorensson

Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh

Maple_LCM, Based on MapleCOMSPS_DRUP --Copyright (c) 2017, Mao Luo, Chu-Min LI,
Fan Xiao: implementing a learnt clause minimisation approach Reference: M. Luo,
C.-M. Li, F. Xiao, F. Manya, and Z. L. , “An effective learnt clause
minimization approach for cdcl sat solvers,” in IJCAI-2017, 2017, pp.703-711.

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

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#define ANTI_EXPLORATION
#define BIN_DRUP

#define GLUCOSE23
// #define INT_QUEUE_AVG
// #define LOOSE_PROP_STAT

#ifdef GLUCOSE23
#define INT_QUEUE_AVG
#define LOOSE_PROP_STAT
#endif

#include <unordered_set>

#include "core/PrintFlags.h"
#include "core/SolverTypes.h"
#include "core/Statistic.h"
#include "mtl/Alg.h"
#include "mtl/Heap.h"
#include "mtl/MDD.h"
#include "mtl/Queue.h"
#include "mtl/Vec.h"
#include "mtl/Vec2.h"
#include "utils/Options.h"

// Don't change the actual numbers.
#define LOCAL 0
#define TIER2 2
#define CORE 3

#define NON -7

namespace Minisat {

/********************* SAT TIME **************************************/

typedef int CRefLS;

class ClauseLS {
  unsigned nbTrueLit;
  unsigned criV;
  int lastSatV;
  int mostRecentV;
  int unSATidx;
  int gt0sz;

 public:
  CRef cr;

  ClauseLS(CRef cr_)
      : nbTrueLit(0),
        criV(0),
        lastSatV(-1),
        mostRecentV(-1),
        unSATidx(-1),
        gt0sz(0),
        cr(cr_) {};
  unsigned nbTrue() const { return nbTrueLit; }
  void setNbTrue(int i) { nbTrueLit = i; }
  unsigned criVar() const { return criV; }
  void setCriVar(int v) { criV = v; }
  int lastSatVar() const { return lastSatV; }
  void setLastSatVar(int v) { lastSatV = v; }
  int mostRecent() const { return mostRecentV; }
  void setMostRecent(int v) { mostRecentV = v; }
  int unSATindex() const { return unSATidx; }
  void setUnSATindex(int i) { unSATidx = i; }
  int gt0size() const { return gt0sz; }
  void setGt0size(int s) { gt0sz = s; }
};

/********************* Solver -- the main class: *********************/

class Solver {
 private:
  template <typename T>
  class MyQueue {
    int max_sz, q_sz;
    int ptr;
    int64_t sum;
    vec<T> q;

   public:
    MyQueue(int sz) : max_sz(sz), q_sz(0), ptr(0), sum(0) {
      assert(sz > 0);
      q.growTo(sz);
    }
    inline bool full() const { return q_sz == max_sz; }
#ifdef INT_QUEUE_AVG
    inline T avg() const {
      assert(full());
      return sum / max_sz;
    }
#else
    inline double avg() const {
      assert(full());
      return sum / (double)max_sz;
    }
#endif
    inline void clear() {
      sum = 0;
      q_sz = 0;
      ptr = 0;
    }
    void push(T e) {
      if (q_sz < max_sz)
        q_sz++;
      else
        sum -= q[ptr];
      sum += e;
      q[ptr++] = e;
      if (ptr == max_sz) ptr = 0;
    }
  };

 public:
  /********************* Constructor/Destructor: *********************/
  Solver();
  virtual ~Solver();

  /*********************  Problem specification: *********************/

  /* Add a new variable with parameters specifying variable mode. */
  Var newVar(bool polarity = false, bool dvar = true);

  /* Add a clause to the solver. */
  bool addClause(const vec<Lit>& ps);

  /* Add the empty clause, making the solver contradictory. */
  bool addEmptyClause();

  /* Add a unit clause to the solver. */
  bool addClause(Lit p);

  /* Add a binary clause to the solver. */
  bool addClause(Lit p, Lit q);

  /* Add a ternary clause to the solver. */
  bool addClause(Lit p, Lit q, Lit r);

  /* Add a clause to the solver without making superflous internal copy. Will
   * change the passed vector 'ps'. */
  bool addClause_(vec<Lit>& ps, int64_t weight = 1);

  /************************* Solving: ********************************/

  /* Removes already satisfied clauses. */
  bool simplify(bool simplifyOriginal = false);

  /* Search for a model that respects a given set of assumptions. */
  bool solve(const vec<Lit>& assumps);

  /* Search for a model that respects a given set of assumptions (With resource
   * constraints). */
  lbool solveLimited(const vec<Lit>& assumps);

  /* Search without assumptions. */
  bool solve();

  /* Search for a model that respects a single assumption. */
  bool solve(Lit p);

  /* Search for a model that respects two assumptions. */
  bool solve(Lit p, Lit q);

  /* Search for a model that respects three assumptions. */
  bool solve(Lit p, Lit q, Lit r);

  /* FALSE means solver is in a conflicting state */
  bool okay() const;

  /************ Write CNF to file in DIMACS-format. ******************/
  void toDimacs(FILE* f, const vec<Lit>& assumps);
  void toDimacs(const char* file, const vec<Lit>& assumps);
  void toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max);

  /************ Convenience versions of 'toDimacs()': ****************/
  void toDimacs(const char* file);
  void toDimacs(const char* file, Lit p);
  void toDimacs(const char* file, Lit p, Lit q);
  void toDimacs(const char* file, Lit p, Lit q, Lit r);

  /*************************** Variable mode: ************************/

  /* Declare which polarity the decision heuristic should use for a variable.
   * Requires mode 'polarity_user'. */
  void setPolarity(Var v, bool b);

  /* Declare if a variable should be eligible for selection in the decision
   * heuristic. */
  void setDecisionVar(Var v, bool b);

  /*************************** Read state: ***************************/

  /* The current assignment of a variable. */
  lbool value(Var x) const;

  /* The current assignment of a literal. */
  lbool value(Lit p) const;

  /* The value of a variable in the last model. The last call to solve must have
   * been satisfiable. */
  lbool modelValue(Var x) const;

  /* The value of a literal in the last model. The last call to solve must have
   * been satisfiable. */
  lbool modelValue(Lit p) const;

  /* The current number of assigned literals. */
  int nAssigns() const;

  /* The current number of original clauses. */
  int nClauses() const;

  /* The current number of learnt clauses. */
  int nLearnts() const;

  /* The current number of variables. */
  int nVars() const;

  int nFreeVars() const;

  /*********************  Resource contraints: ***********************/
  void setConfBudget(int64_t x);
  void setPropBudget(int64_t x);
  void budgetOff();

  /* Trigger a (potentially asynchronous) interruption of the solver. */
  void interrupt();

  /* Clear interrupt indicator flag. */
  void clearInterrupt();

  /*********************  Memory managment: **************************/

  virtual void garbageCollect();
  bool toGarbageCollect();
  void checkGarbage();

  /**********************  Extra results: ****************************/
  /* If problem is satisfiable, this vector contains the model (if any). */
  vec<lbool> model;

  /* If problem is unsatisfiable (possibly under assumptions), this vector
   * represent the final conflict clause expressed in the assumptions. */
  vec<Lit> conflict;

  /*********************  Mode of operation: *************************/
  FILE* drup_file;

  /* Log level: (0=silent, 1=some, 2=more). */
  int verbosity;

  // [LRB]: TODO
  double step_size;

  // [LRB]: TODO
  double step_size_dec;

  // [LRB]: TODO
  double min_step_size;

  /* The left conflicts times to update 'var_decay'. */
  int timer;

  double var_decay;

  double clause_decay;

  double random_var_freq;

  double random_seed;

  /* True for VSIDS phase, False for LRB phase. */
  bool VSIDS;

  /* Controls conflict clause minimization (0=none, 1=basic, 2=deep). */
  int ccmin_mode;

  /* Controls the level of phase saving (0=none, 1=limited, 2=full). */
  int phase_saving;

  bool rnd_pol;  // Use random polarities for branching heuristics.

  /* Initialize variable activities with a small random value. */
  bool rnd_init_act;

  /* The fraction of wasted memory allowed before a garbage collection is
   * triggered. */
  double garbage_frac;

  int restart_first;  // The initial restart limit (default 100).

  /* The factor with which the restart limit is multiplied in each restart
   * (default 1.5).*/
  double restart_inc;

  /* The intitial limit for learnt clauses is a factor of the original clauses
   * (default 1 / 3). */
  double learntsize_factor;

  /* The limit for learnt clauses is multiplied with this factor each restart
   * (default 1.1). */
  double learntsize_inc;

  int learntsize_adjust_start_confl;
  double learntsize_adjust_inc;

  /*********************  Statistics: ********************************/

  uint64_t solves;           // The number of calls to 'solve_()'.
  uint64_t starts;           // The number of restarts.
  uint64_t decisions;        // The number of decisions.
  uint64_t rnd_decisions;    // The number of random decisions.
  uint64_t propagations;     // The number of propagations.
  uint64_t conflicts;        // The number of conflicts.
  uint64_t conflicts_VSIDS;  // The number of conflicts in VSIDS phase.

  /* Count the number of decision variables in the 'decision' vector. */
  uint64_t dec_vars;

  uint64_t clauses_literals;  // The number of literals in original clauses.

  uint64_t learnts_literals;  // The number of literals in learnt clauses.

  /* The number of literals in learnt clauses before simplify. */
  uint64_t max_literals;

  /* The number of literals in learnt clauses after simplify. */
  uint64_t tot_literals;

  /* [LRB] for each variable, record the current 'conflicts' value when it is
   * enqueued. Used for calculating variable's age and activity. */
  vec<uint32_t> picked;

  /* [LRB] for each variable, record the number of conflicts related to it. */
  vec<uint32_t> conflicted;

  vec<uint32_t> almost_conflicted;
#ifdef ANTI_EXPLORATION
  vec<uint32_t> canceled;
#endif

 protected:
  /*********************  Helper structures: *************************/

  struct VarData {
    CRef reason;
    int level;
    int index;
  };
  static inline VarData mkVarData(CRef cr, int l, int i) {
    VarData d = {cr, l, i};
    return d;
  }

  struct Watcher {
    CRef cref;
    Lit blocker;
    Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
    bool operator==(const Watcher& w) const { return cref == w.cref; }
    bool operator!=(const Watcher& w) const { return cref != w.cref; }
  };

  struct WatcherDeleted {
    const ClauseAllocator& ca;
    WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
    bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
  };

  struct VarOrderLt {
    const vec<double>& activity;
    bool operator()(Var x, Var y) const { return activity[x] > activity[y]; }
    VarOrderLt(const vec<double>& act) : activity(act) {}
  };

  struct VarOrderGt {
    const vec<double>& activity;
    bool operator()(Var x, Var y) const { return activity[x] < activity[y]; }
    VarOrderGt(const vec<double>& act) : activity(act) {}
  };

  struct LitOrderWeightDec {
    const vec<int64_t>& weights;
    bool operator()(Lit x, Lit y) const {
      return weights[var(x)] > weights[var(y)];
    }
    LitOrderWeightDec(const vec<int64_t>& w) : weights(w) {}
  };

  struct LitOrderWeightInc {
    const vec<int64_t>& weights;
    bool operator()(Lit x, Lit y) const {
      return weights[var(x)] < weights[var(y)];
    }
    LitOrderWeightInc(const vec<int64_t>& w) : weights(w) {}
  };

  struct VarOrderWeightDec {
    const vec<int64_t>& weights;
    bool operator()(Var x, Var y) const { return weights[x] > weights[y]; }
    VarOrderWeightDec(const vec<int64_t>& w) : weights(w) {}
  };

  struct VarOrderWeightActivityDec {
    const vec<int64_t>& weights;
    const vec<double>& activity;
    bool operator()(Var x, Var y) const {
      return weights[x] > weights[y] ||
             (weights[x] == weights[y] && activity[x] < activity[y]);
    }
    VarOrderWeightActivityDec(const vec<int64_t>& w, const vec<double>& a)
        : weights(w), activity(a) {}
  };

  struct LitOrderPartition {
    const vec<int64_t>& weights;
    vec2<Lit, vec<Lit>>& conflictLits;
    bool operator()(Lit x, Lit y) const {
      return conflictLits[x].size() < conflictLits[y].size() ||
             conflictLits[x].size() == conflictLits[y].size() &&
                 weights[var(x)] > weights[var(y)];
    }
    LitOrderPartition(const vec<int64_t>& w, vec2<Lit, vec<Lit>>& c)
        : weights(w), conflictLits(c) {}
  };

  struct LitOrderPartitionInverse {
    const vec<int64_t>& weights;
    vec2<Lit, vec<Lit>>& conflictLits;
    bool operator()(Lit x, Lit y) const {
      return conflictLits[x].size() > conflictLits[y].size() ||
             conflictLits[x].size() == conflictLits[y].size() &&
                 weights[var(x)] > weights[var(y)];
    }
    LitOrderPartitionInverse(const vec<int64_t>& w, vec2<Lit, vec<Lit>>& c)
        : weights(w), conflictLits(c) {}
  };

  struct SkipCoresOrder {
    const vec<int>& countL;
    const vec<int>& minL;
    bool operator()(int i, int j) const {
      return countL[i] > countL[j] ||
             (countL[i] == countL[j] && minL[i] < minL[j]);
    }
    SkipCoresOrder(const vec<int>& cL, const vec<int>& mL)
        : countL(cL), minL(mL) {}
  };

  /* A soft literal in core with the locked weights. */
  struct coreLit {
    Lit lit;         // The soft literal in the owner core.
    int64_t weight;  // The locked soft weight by the owner core.

    coreLit(Lit l, int64_t w) : lit(l), weight(w) {};
    coreLit() {};
  };

  struct CoreLitOrderWeightInc {
    bool operator()(coreLit x, coreLit y) const { return x.weight < y.weight; }
    CoreLitOrderWeightInc() {}
  };

  struct CoreLitOrderWeightDec {
    bool operator()(coreLit x, coreLit y) const { return x.weight > y.weight; }
    CoreLitOrderWeightDec() {}
  };

  struct CoreLitLessThanTrailIndex {
    const vec<VarData>& vardata;
    CoreLitLessThanTrailIndex(const vec<VarData>& vd) : vardata(vd) {}
    bool operator()(const coreLit& x, const coreLit& y) const {
      return vardata[var(x.lit)].index < vardata[var(y.lit)].index;
    }
  };

  // Helper for 'setLitWeightBeforeCancelAssignment', record the weights for the
  // soft literals to create a new core.
  struct assistantWeight {
    int64_t freeWeight;  // remaining weight for the soft lit in new core, eg5:
                         // rw(s1)
    // eg5: wlock(s1, c1) + wlock(s1, c2) + xxx
    int64_t inSubcoreWeight;  // the sum of locked weights in unlocked cores.
    assistantWeight(int64_t fw, int64_t iw)
        : freeWeight(fw), inSubcoreWeight(iw) {};
    assistantWeight() : freeWeight(0), inSubcoreWeight(0) {};
    void reset() {
      freeWeight = 0;
      inSubcoreWeight = 0;
    }
    int64_t sum() {
      assert(freeWeight >= 0 && inSubcoreWeight >= 0);
      return freeWeight + inSubcoreWeight;
    }
  };

  /* A local core is a subset of soft clauses that cannot all be satisfied
   * without falsifying a hard clause at the current search tree node. */
  struct LocalCore {
    vec<coreLit> coreLits;  // The vector of soft literals in the core.

    /* The reason of this core (soft conflict). Produced by analyse the
     * unit propagate of soft literals. */
    vec<Lit> reasons;

    /* The weight of this core, equals the minimal weights of all the locked
     * soft literals. */
    int64_t weight;

    /* The total weights of all the failed soft literals in UP. The core can be
     * unlocked when falsifiedWeight >= weight. */
    int64_t falsifiedWeight;

    int level;  // The decision level when the core is created.

    /* Mark if the core is processed in conflict analysis. */
    bool seen;

    /* Mark the index of the current trail when the core is unlocked. Will be
     * used when compute the weight of new created core. */
    int unlockedIndex;

    LocalCore()
        : coreLits(),
          reasons(),
          weight(0),
          falsifiedWeight(0),
          level(0),
          seen(false),
          unlockedIndex(-1) {};

    /* Clear all the data in this core for recycle purpose. */
    void reset() {
      coreLits.clear();
      reasons.clear();
      weight = 0;
      falsifiedWeight = 0;
      level = 0;
      seen = false;
      unlockedIndex = -1;
    }
  };

  /*********************  Solver state: ******************************/

  /* If FALSE, the constraints are already unsatisfiable. No part of the solver
   * state may be used! */
  bool ok;

  vec<CRef> clauses;  // List of problem clauses.

  vec<CRef> learnts_core;   // List of core learnt clauses.
  vec<CRef> learnts_tier2;  // List of tier2 learnt clauses.
  vec<CRef> learnts_local;  // List of local learnt clauses.

  double cla_inc;  // Amount to bump next clause with.

  /* Conflict history base measurement for variables branching priority. */
  vec<double> activity_CHB;

  /* Variable State Independent Decaying Sum measurement for variables branching
   * priority. */
  vec<double> activity_VSIDS;

  double var_inc;  // Amount to bump next variable with.

  /* Watches for binary clauses only. */
  OccLists<Lit, vec<Watcher>, WatcherDeleted> watches_bin;

  /* 'watches[lit]' is a list of constraints watching 'lit' (will  go there if
   * literal becomes true). */
  OccLists<Lit, vec<Watcher>, WatcherDeleted> watches;

  vec<lbool> assigns;  // The current assignments vector.

  vec<char> polarity;  // The preferred polarity of each variable.

  /* Declares if a variable is eligible for selection in the decision heuristic.
   */
  vec<char> decision;

  /* Assignment stack; stores all assigments made in the order they were made.
   */
  vec<Lit> trail;

  /* Separator indices for different decision levels in 'trail'. */
  vec<int> trail_lim;

  vec<VarData> vardata;  // Stores reason and level for each variable.

  /* Head of queue (as index into the trail -- no more explicit propagation
   * queue in MiniSat). */
  int qhead;

  /* Number of top-level assignments since last execution of 'simplify()'. */
  int simpDB_assigns;

  /* Remaining number of propagations that must be made before next execution of
   * 'simplify()'. */
  int64_t simpDB_props;

  /* Current set of assumptions provided to solve by the user. */
  vec<Lit> assumptions;

  /* A priority queue of variables ordered with respect to the variable
   * activity, order_heap_distance. */
  Heap<VarOrderLt> order_heap_CHB, order_heap_VSIDS;

  double progress_estimate;  // Set by 'search()'.

  /* Indicates whether possibly inefficient linear scan for satisfied clauses
   * should be performed in 'simplify'. */
  bool remove_satisfied;

  int core_lbd_cut;
  float global_lbd_sum;

  /* For computing moving averages of recent LBD values. */
  MyQueue<int> lbd_queue;

  uint64_t next_T2_reduce, next_L_reduce;

  /* Clause memory manager and grabage collector. */
  ClauseAllocator ca;

  /* Temporaries (to reduce allocation overhead). Each variable is prefixed by
   * the method in which it is used, exept 'seen' wich is used in several
   * places. */
  vec<char> seen;

  vec<Lit> analyze_stack;

  vec<Lit> analyze_toclear;

  /* Auxiliary vector to store the literals for a clause. Remember to clear
   * before/after it. */
  vec<Lit> add_tmp;

  vec<Lit> add_oc;

  /* Mostly for efficient LBD computation. 'seen2[i]' will indicate if decision
   * level or variable 'i' has been seen. */
  vec<uint64_t> seen2;

  uint64_t counter;  // Simple counter for marking purpose with 'seen2'.

  double max_learnts;
  double learntsize_adjust_confl;
  int learntsize_adjust_cnt;

  /********************* Resource contraints : ***********************/

  int64_t conflict_budget;     // -1 means no budget.
  int64_t propagation_budget;  // -1 means no budget.
  bool asynch_interrupt;

  /********************* Main internal methods: **********************/

  /* Insert a variable in the decision order priority queue. */
  void insertVarOrder(Var x);

  /* Return the next decision variable. */
  Lit pickBranchLit();

  /* Begins a new decision level. */
  void newDecisionLevel();

  /* Enqueue a literal. Assumes value of literal is undefined. */
  void uncheckedEnqueue(Lit p, CRef from = CRef_Undef);

  /* Test if fact 'p' contradicts current state, enqueue otherwise. */
  bool enqueue(Lit p, CRef from = CRef_Undef);

  /* Perform unit propagation. Returns possibly conflicting clause. */
  CRef propagate();

  /* Backtrack until a certain level. */
  void cancelUntil(int level);

  void analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel,
               int& out_lbd);

  /* COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE
   * GENERALIZATION? */
  void analyzeFinal(Lit p, vec<Lit>& out_conflict);

  /* (helper method for 'analyze()') */
  bool litRedundant(Lit p, uint32_t abstract_levels);

  /* Search for a given number of conflicts. */
  lbool search(int& nof_conflicts);

  /* Main solve method (assumptions given in 'assumptions'). */
  lbool solve_();

  /* Reduce the set of learnt clauses. */
  void reduceDB();
  void reduceDB_Tier2();

  /* Shrink 'cs' to contain only non-satisfied clauses. */
  void removeSatisfied(vec<CRef>& cs);

  void safeRemoveSatisfied(vec<CRef>& cs, unsigned valid_mark);

  void rebuildOrderHeap();

  /* Further learnt clause minimization by binary resolution. */
  bool binResMinimize(vec<Lit>& out_learnt);

  /*********** Maintaining Variable/Clause activity: *****************/

  /* Decay all variables with the specified factor. Implemented by increasing
   * the 'bump' value instead. */
  void varDecayActivity();

  /* Increase a variable with the current 'bump' value. */
  void varBumpActivity(Var v, double mult);

  /* Decay all clauses with the specified factor. Implemented by increasing the
   * 'bump' value instead. */
  void claDecayActivity();

  /* Increase a clause with the current 'bump' value. */
  void claBumpActivity(Clause& c);

  /********************* Operations on clauses: **********************/

  /* Attach a clause to watcher lists. */
  void attachClause(CRef cr);

  /* Detach a clause to watcher lists. */
  void detachClause(CRef cr, bool strict = false);

  /* Detach and free a clause. */
  void removeClause(CRef cr);

  /* Returns TRUE if a clause is a reason for some implication in the current
   * state. */
  bool locked(const Clause& c) const;

  /* Returns TRUE if a clause is satisfied in the current state. */
  bool satisfied(const Clause& c, bool checkFullAssignments = false) const;

  void relocAll(ClauseAllocator& to);

  /********************* Misc: ***************************************/

  /* Gives the current decisionlevel. */
  int decisionLevel() const;

  /* Used to represent an abstraction of sets of decision levels. */
  uint32_t abstractLevel(Var x) const;

  CRef reason(Var x) const;

  int level(Var x) const;

  int trailIndex(Var x) const;

  /* DELETE THIS ?? IT'S NOT VERY USEFUL ... */
  double progressEstimate() const;
  bool withinBudget() const;

  template <class V>
  int computeLBD(const V& c) {
    int lbd = 0;

    counter++;
    for (int i = 0; i < c.size(); i++) {
      int l = level(var(c[i]));
      if (l != 0 && seen2[l] != counter) {
        seen2[l] = counter;
        lbd++;
      }
    }

    return lbd;
  }

  /********************* Static helpers: *****************************/

  /* Returns a random float 0 <= x < 1. Seed must never be 0. */
  static inline double drand(double& seed) {
    seed *= 1389796;
    int q = (int)(seed / 2147483647);
    seed -= (double)q * 2147483647;
    return seed / 2147483647;
  }

  /* Returns a random integer 0 <= x < size. Seed must never be 0. */
  static inline int irand(double& seed, int size) {
    return (int)(drand(seed) * size);
  }

  /********************* simplify ************************************/

 public:
#ifdef BIN_DRUP
  static int buf_len;
  static unsigned char drup_buf[];
  static unsigned char* buf_ptr;

  static inline void byteDRUP(Lit l) {
    unsigned int u = 2 * (var(l) + 1) + sign(l);
    do {
      *buf_ptr++ = u & 0x7f | 0x80;
      buf_len++;
      u = u >> 7;
    } while (u);
    *(buf_ptr - 1) &= 0x7f;  // End marker of this unsigned number.
  }

  template <class V>
  static inline void binDRUP(unsigned char op, const V& c, FILE* drup_file) {
    assert(op == 'a' || op == 'd');
    *buf_ptr++ = op;
    buf_len++;
    for (int i = 0; i < c.size(); i++) byteDRUP(c[i]);
    *buf_ptr++ = 0;
    buf_len++;
    if (buf_len > 1048576) binDRUP_flush(drup_file);
  }

  static inline void binDRUP_strengthen(const Clause& c, Lit l,
                                        FILE* drup_file) {
    *buf_ptr++ = 'a';
    buf_len++;
    for (int i = 0; i < c.size(); i++)
      if (c[i] != l) byteDRUP(c[i]);
    *buf_ptr++ = 0;
    buf_len++;
    if (buf_len > 1048576) binDRUP_flush(drup_file);
  }

  static inline void binDRUP_flush(FILE* drup_file) {
    fwrite(drup_buf, sizeof(unsigned char), buf_len, drup_file);
    buf_ptr = drup_buf;
    buf_len = 0;
  }
#endif
  inline void fixBinClauseOrder(Clause& c);
  bool simplifyAll();
  bool simplifyLearnt(Clause& c, CRef cr, vec<Lit>& lits);
  bool simplifyLearnt_core();
  bool simplifyLearnt_tier2();
  bool simplifyOriginalClauses(vec<CRef>& clauseSet);

  /* Record current trail size and data structures relate to the current
   * assignment. */
  void setTrailRecord();

  /* Resume the context state to last record point. */
  void resetTrailRecord();

  /* Withdraw the assignments by propagation and do 'resetTrailRecord'. */
  void cancelUntilTrailRecord();

  /* Same as 'cancelUntilTrailRecord' and clear the 'seen'.  */
  void cancelUntilTrailRecordUnsee();

  /* Same as 'cancelUntilTrailRecord' and update the activities of soft literals
   * in 'orderHeapLookahead'.  */
  void cancelUntilTrailRecordFillHeap();

  void simpleUncheckEnqueue(Lit p, CRef from = CRef_Undef);

  CRef simplePropagate();

  CRef simplePropagateForAMO(vec<Lit>& trueLits);

  /* [LA] lookahead context of current trail stack length. */
  int trailRecord;

  uint64_t nbSimplifyAll;

  uint64_t simplified_length_record;

  uint64_t original_length_record;

  uint64_t s_propagations;

  int nbGrbgCllct;

  vec<Lit> simp_learnt_clause;

  long curSimplify;

  uint64_t nbconfbeforesimplify;

  int incSimplify;

  vec<double> var_iLevel;

  vec<double> var_iLevel_tmp;

  uint64_t nbcollectfirstuip;

  uint64_t nblearntclause;

  uint64_t nbDoubleConflicts;

  uint64_t nbTripleConflicts;

  int uip1;

  int uip2;

  vec<int> pathCs;

  uint64_t previousStarts;

  double var_iLevel_inc;

  vec<Lit> involved_lits;

  double my_var_decay;

  vec<CRef> usedClauses;

  bool removed(CRef cr);
  void simplifyConflictClause(vec<Lit>& out_learnt, int& out_btlevel,
                              int& out_lbd);
  void analyzeSoftConflict(vec<Lit>& out_learnt, int& out_btlevel,
                           int& out_lbd);
  void getConflictingClause(vec<Lit>& conflictClause, int& maxConflLevel);
  void getConflictingClauseSimple(vec<Lit>& conflictClause, int& maxConflLevel);
  void seeReasons(vec<Lit>& conflictClause, int& maxConflLevel,
                  vec<Lit>& reasons);
  void seeReason(vec<Lit>& conflictClause, int& maxConflLevel, Lit q);

  vec<CRef> falseSoftClauses;

  /* The database to store all the soft clauses. */
  vec<CRef> softClauses;

  vec<int> falseSoftClauses_lim;

  /* The number of soft conflicts. */
  uint64_t softConflicts;

  /* The number of literals in all the soft conflicts. */
  uint64_t softLiterals;

  /* Marked as true when learning a new soft clause. Cleared after adding the
   * newly learned clause into database. */
  bool softConflictFlag;

  struct softWatcher {
    CRef cref;
    softWatcher(CRef cr) : cref(cr) {}
    bool operator==(const softWatcher& w) const { return cref == w.cref; }
    bool operator!=(const softWatcher& w) const { return cref != w.cref; }
  };

  int64_t totalWeight;

  unsigned int weight;

  int instanceType;

  int nbOriVars;

  int nbClauseReduce;

  int falseSoftClausesRecord;

  int nbOrignalVars;

  void simpleAnalyzeSoftConflict(vec<Lit>& out_learnt);

  bool simplifyLearnt_local();

  void addHardClausesForSoftClauses();

  inline bool isSoftLits(Var v);

  inline bool isSoftLits(Lit p);

  inline void getClauseLits(Clause& c, vec<Lit>& v);

  void reduceDB_core();

  vec<Lit> falseLits;  // Collection of false literals in current node.

  vec<int> falseLits_lim;

  int falseLitsRecord;

  // Record the sum of the core weights of all the detected cores by lookahead.
  int64_t lookaheadConflictCost;

  // TODO: ???
  vec<int64_t> countedWeight_lim;

  // TODO: ???
  vec<int64_t> satisfiedWeight_lim;

  int64_t nonInferenceCost;

  int64_t updateCost;

  int next_C_reduce;

  /* [RL] the number of unit propagation triggered by lookahead. */
  uint64_t lk_propagations;

  /* [RL] the sum of LB. */
  int64_t totalPrunedLB;

  /* [RL] the sum of LB square. TODO: check overflow? */
  int64_t totalPrunedLB2;

  /* [AUX] the current falsied soft literal by lookahead propagation. */
  Var falseVar;

  /* [AUX] the weight of current 'falseVar'. */
  int64_t falseVarWeight;

  /* [AUX] the trail index limitation for lookahead propagation. */
  int trailIndexLimit = 0;

  /* [AUX] how many propagation steps are allowed after found the first falseVar
   * or falseCore. */
  int trailIndexLimitDelta = 100;

  /* Clear all the false var related data. */
  void clearFalseVar() {
    falseVar = var_Undef;
    falseVarWeight = 0;
  }

  /* [AUX] when the core weight decreased to 0, the core is unlocked and will be
   * recorded here. */
  int falseCore;

  /* [AUX] the initial weight of current 'falseCore'. */
  int64_t falseCoreInitWeight;

  /* [AUX] one BCP may falsify multiple cores, record them all here
   * and select the false core with the highest initial weight as the real
   * falseCore. */
  std::unordered_set<int> allFalseCores;

  /* Clear all the false cores related data. */
  void clearFalseCores() {
    falseCore = core_Undef;
    falseCoreInitWeight = 0;
    allFalseCores.clear();
  }

  /* Sort core lits by their weights and use minimal lits to unlock the core. */
  int64_t getFalseCoreInitialWeight(int core_id);

  vec<CRef> hardSoftClauses;

  vec<Lit> imply;

  char* litStrBuffer;
  const char* lit2str(Lit lit);

  /* [LA] The queue contains soft literals from recent conflicts for lookahead
   * search. Lits in this queue have higher priority than lits in the
   * 'orderHeapLookahead'. */
  Heap<VarOrderWeightDec> lastConflLits;

  /* The variable selecting queue for soft literals. The variabls in it are
   * sorted by their activities in 'activityLB'. */
  Heap<VarOrderWeightActivityDec> orderHeapLookahead;

  /* The activity for soft variables in 'orderHeapLookahead'. */
  vec<double> activityLB;

  /* Control the learning rate for Q-learning. */
  double stepSizeLB;

  uint64_t subconflicts;  // to control iterative calls of search()

  int64_t fixedCostBySearch;

  int64_t derivedCost;

  bool enqueueAssumptions(int& nextIdx, bool recheckNext);

  void lookbackResetTrail(CRef confl, Var falseVar, vec<Lit>& out_learnt,
                          int core, int64_t& minSetCost, bool resDone,
                          int64_t remainingCost = INT64_MAX);

  CRef propagateForLK();

  /* Put a literal in queue during lookahead propagation. Raise a soft conflict
   * if an unlocked soft literal is falsified. */
  bool uncheckedEnqueueForLK(Lit p, CRef from = CRef_Undef);

  bool redundantLit(Lit p);

  void insertSoftLitOrder(Var x);

  /* Pick a soft var for propagating in lookahead. */
  Var pickLookaheadVar();

  void removeLearntClauses();

  void cancelUntilUB();

  void checkSolution();

  void checkSolutionLS();

  bool findConflictSoftLits();

  void partition2();

  void addConflictLit(Lit p, Lit q);

  Lit createHardClausesFromLits(vec<Lit>& lits, int64_t weight);

  /* Propagate with harden. */
  CRef lPropagate();

  vec<int> softVarLocked;

  vec<int> unLockedVars_lim;

  int unLockedVarsRecord;

  vec<CRef> hardens;

  vec<int> hardens_lim;

  vec<bool> hardened;

  uint64_t fixedByHardens;

  int staticNbVars;

  void cleanClausesForNewVars(vec<CRef>& cs);

  int setCounter(CRef cr);

  int countCommunLiterals(CRef cr);

  void splitClauses(vec<CRef>& cs);

  void identifyClausesToSplit(vec<CRef>& cs);

  uint64_t nbSavedLits;

  /* Contains all literals belonging to the ith iset. */
  vec<LocalCore> localCores;

  /* The collection of all the variables in cores. */
  vec<Var> varsInCores;

  /* Contains the indexes of cores where 'v' belongs to. */
  vec2<Var, vec<int>> coresOfVar;

  bool restoredLitFlag;

  int tier2_lbd_cut;

  int coreLimit;

  int coreInactiveLimit;

  int tier2Limit;

  int tier2InactiveLimit;

  uint64_t quasiSoftConflicts;

  uint64_t fixedByQuasiConfl;

  void cleanCores();

  void simpleuncheckedEnqueueForLK(Lit p, CRef from = CRef_Undef);

  CRef simplepropagateForLK();

  void desactivateSoftLits();

  void activateSoftLits();

  void getAllUIP(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);

  bool hardenFromQuasiSoftConflict();

  void simplifyQuasiConflictClause(vec<Lit>& out_learnt, int& out_btlevel,
                                   int& out_lbd);

  /********************* PB Constraint Start *************************/

  vec2<int, vec<Lit>> amos;

  vec<int> amosOfVar;

  vec<Var> dynVars;

  bool CCPBadded;

  bool GACPBadded;

  vec<CRef> PBC;

  void partitionAMO();

  bool findAMOs();

  Var newAuxiVar(bool sign = false);

  bool dynVar(Var v);

  void collectDynVars();

  void addPBConstraints();

  void addPBConstraintMDD(vec2<int, vec<int64_t>>& Q, vec2<int, vec<Lit>>& X,
                          int k);

  Lit addPBConstraintMDD(MDD* mdd, vec2<int, vec<Lit>>& X, vec<Lit>& asserted,
                         bool trueNode);

  void addPBConstraintGPW(vec2<int, vec<int64_t>>& Q, vec2<int, vec<Lit>>& X,
                          int64_t K);

  void addPBConstraintMTO(vec2<int, vec<int64_t>>& coefs,
                          vec2<int, vec<Lit>>& activeSoftLits, int64_t k);

  void nLevelsMTO(vec2<int, vec<int64_t>>& q, vec2<int, vec<Lit>>& x,
                  int lIndex, int m, vec<Lit>& result);

  inline Lit mtoCreate(Lit& p);

  inline bool nthBit(int64_t x, int n);

  inline void addPBClause(vec<Lit>& v);

  Var newAuxiVarForPB();

  /******************** PB Constraint End ****************************/

  /********************* Core and Lock Start *************************/

  vec<int> activeCores;

  vec<int> freeCores;

  vec<int> lastCores;

  int totalNbConflsL;

  int savedNbConflsL;

  int totalNbConflsFailL;

  int savedNbConflsFailL;

  bool coreConflictIn0;

  /* [AUX] record the propagated soft literals to form the new core. Used to
   * calculate the weight of new core. eg5: s6, s1, s4 in the binary tree. */
  vec<Lit> keyAssignment;

  vec<assistantWeight> keyAssignmentWeight;

  vec<coreLit> newcoreLits;

  vec<Lit> newcoreReason;

  vec<int> assignedVars;

  int64_t setInitialWeight();

  void setLitWeightBeforeCancelAssignment(int coreid);

  void updateCoreAfterAssignment(int coreid);

  void updateCoresAfterAssignment();

  int pickCoreIdx();

  void resetCoresData();

  void recoverAffectedCoresAfterLookahead(int skipCoreId);

  void setNewcoreReason(int coreid);

  void cleanSubcores();

  void setCoreMultilock(int coreIdx);

  /********************* Core and Lock End ***************************/

  /********************* Lookahead Start *****************************/

  struct Qscore {
    double yes;
    double no;
    Qscore(double yes_, double no_) : yes(yes_), no(no_) {}
  };

  /* For different number of false soft lits in current assignment, record the
   * success and nosuccess rate of lookahead. */
  vec<Qscore> Qscores;

  /* The number of skipped lookahead by Qlearning or lb heuristic. */
  int skipLA;

  /* The number of skipped lookahead by Qlearning. */
  int skipLAbyprba;

  uint64_t LOOKAHEAD;         // The total number of lookahead.
  uint64_t nbLKsuccess;       // The number of successful lookahead.
  uint64_t savedLOOKAHEAD;    // Save 'LOOKAHEAD' for last search.
  uint64_t savednbLKsuccess;  // Save 'nbLKsuccess' for last search.

  int64_t rootConflCost;
  bool redoLookahead;
  int REDO_LOOKAHEAD;

  /* Firstly, do lookahead without core unlock. If failed, then do lookahead
   * with core unlock. */
  void todoLookahead();

  /* Do lookahead with reinforcement learning.
   * Return True iff lookahead was done and some propagation was done or LB was
   * computed. */
  bool lookaheadQscore();

  void moreLookahead();

  void setCore(int core, int64_t coreCost);

  void resetConflicts();

  void resetConflicts_();

  /* Record the realted cores id when detecting a new core. */
  vec<int> affectedCores;

  /* Keep all the unlocked literals. */
  vec<int> unlockedVars;

  /* For each unlocked var, record the core to unlock it. eg: literal s1 is in
   * cores {c1, c2, c3}. If s1 unlocked by c1, then unlockCoreOfVar[s1] = c1. */
  vec<int> unlockCoreOfVar;

  /* [AUX] helper to create a new complex core, eg:c1 = {x1, x2, x3}, propagate
   * x4 -> Falsify(x2) -> unlock(c1) -> push c1 into subCores. */
  vec<int> subCores;

  bool TodoSecondLookahead;
  double SECOND_LOOKAHEAD_TIME;

  /* Statistic the number of lookahead with unlock mechanism. */
  uint64_t LOOKAHEAD_MULTILOCKS;

  /* Statistic the number of successful lookahead with unlock mechanism. */
  uint64_t LOOKAHEAD_MULTILOCKS_SUCCS;

  uint64_t LOOKAHEAD_MULTILOCKS_MULTICORES;

  /* Statistic the number of skipped lookahead with unlock mechanism. */
  uint64_t LOOKAHEAD_MULTILOCKS_SKIP;

  /* Return the locked weight of a var by a core. */
  inline int64_t getCorelitWeight(int coreid, Var v) {
    for (int i = 0; i < localCores[coreid].coreLits.size(); i++)
      if (var(localCores[coreid].coreLits[i].lit) == v)
        return localCores[coreid].coreLits[i].weight;
    return -1;
  }

  inline int64_t getCoreWeight(int coreid) { return localCores[coreid].weight; }

  /* Return true if the core is unlocked. */
  inline bool unlockedCore(int coreid) {
    return localCores[coreid].falsifiedWeight >= localCores[coreid].weight;
  }

  /* Return true if a soft variable is unlocked (have available weights). */
  inline bool nonLockedVar(Var v) { return isSoftLits(v) && weights[v] > 0; }

  /* Return true if a soft variable is unlocked (have available weights). */
  inline bool nonLockedLit(Lit l) { return nonLockedVar(var(l)); }

  /* Return true if a locked soft variable is unlocked by any core.*/
  inline bool unlockedVar(Var v) {
    for (int i = 0; i < coresOfVar[v].size(); i++) {
      if (unlockedCore(coresOfVar[v][i])) {
        return true;
      }
    }
    return false;
  }

  /* Check if a clause is in hardens vector. */
  bool conflInHardens(CRef confl);

  /* Collect the unassigned literals in cores for lookahead propagation. */
  vec<Lit> litsTobeAssigned;

  /* Collect the cores id that have unassigned literals. */
  vec<int> coresTobeAssigned;

  void analyzeInAssignCoreLits(vec<Lit>& out_learnt, int coreid);
  void conflictInAssignCoreLits(int i, CRef& confl);
  bool assignmentsInAssignCoreLits();
  bool assignCoreLits(CRef& confl);
  void collectCoreLitsTobeAssigned(int coreid);
  bool uncheckedEnqueueForLKMultilocks(Lit p, CRef from = CRef_Undef);
  CRef propagateForLKMultilocks();
  bool enqueueAssumptionsMultilocks(vec<Lit>& allAssumed);
  Var pickSecondLookaheadVar();
  int seeUnlockLits(Var v, int falseVar);
  int analyzeWithClauseBin();
  int analyzeWithClause(CRef confl, vec<Lit>& out_learnt, int start);
  void analyzeWithConfl(CRef confl, int& pathC, vec<Lit>& out_learnt);
  void analyzeWithFalsevar(int& pathC, vec<Lit>& out_learnt);
  void analyzeWithFalsecore(int& pathC, vec<Lit>& out_learnt);
  void lookbackResetTrailMultilocks(CRef confl, vec<Lit>& out_learnt,
                                    bool resDone, int64_t remainingCost);
  void printAroundSecondLookahead(bool before);
  void printSummaryStat();
  bool todoSecondLookahead();
  void lookaheadMultilocks();

  /********************* Lookahead End *******************************/

  inline int lchild(int i);
  inline int rchild(int i);
  inline int parent(int i);
  void addQuadraticMerge(const vec<Lit>& x1, const vec<Lit>& x2, vec<Lit>& y);
  void addTotalizer(const vec<Lit>& x, vec<Lit>& y);
  vec<CRef> isetClauses;

  double avgAct(vec<CRef>& cs, int& nb0);

  inline void declareSoftLit(Lit p, bool unit = false, int64_t weight = 1);
  inline void removeSoftLit(Lit p);

  /************************ Harden Start *****************************/

  unsigned int nbHardens;
  Heap<VarOrderWeightDec> hardenHeap;

  bool harden();
  Var pickHardenVar();
  void analyzeQuasiSoftConflict(vec<Lit>& out_learnt, int& out_btlevel,
                                int& out_lbd);

  /************************* Harden End ******************************/

  void reduceClause(CRef cr, int pathC);

  void simplereduceClause(CRef cr, int pathC);

  bool fixByLookahead(vec<Lit>& out_learnt);

  void simplelookback(CRef confl, Var falseVar, vec<Lit>& lits,
                      vec<Lit>& out_learnt);

  void updateClauseUse(CRef confl, bool always = false);

  Lit simplePickBranchLit();

  bool failedLiteralDetection();

  int nbFlyReduced;

  int pureSoftConfl;

  uint64_t nbFixedByLH;

  /* The number of conflicts generated by lookahead. */
  uint64_t la_conflicts;

  /* The number of soft conflicts generated by lookahead. */
  uint64_t la_softConflicts;

  /* The current conflict clause returned by lookahead. */
  CRef LHconfl;

  Lit binConfl[2];

  vec<Var> testedVars;

  vec<char> involved;

  /********************* Subsumption Start ***************************/

  vec<CRef> subsumptionQueue;

  inline Lit subsume(const Clause& c, const Clause& d);

  bool subsumeClauses(CRef cr, int& subsumed, int& deleted_literals);

  bool backwardSubsume();

  bool backwardSubsumeAndEliminateEqLits();

  /********************* Subsumption End *****************************/

  /********************* Temporaries: ********************************/

  CRef bwdsub_tmpunit;

  vec<int> nbActiveVars;

  vec<Lit> impliedLits;

  struct ClauseDeleted {
    const ClauseAllocator& ca;
    explicit ClauseDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
    bool operator()(const CRef& cr) const { return ca[cr].mark() == 1; }
  };

  void removeClauseFromOccur(CRef dr, bool strict = false);

  void collectClauses(vec<CRef>& clauseSet, int learntType = CORE);

  bool simpleStrengthenClause(CRef cr, Lit l);

  void cancelUntilTrailRecord1();

  /********************* SAT TIME START ******************************/

  vec2<Var, vec<Var>> neibors;
  vec2<Lit, vec<CRefLS>> inClauses;
  vec<int> score;
  vec<double> Vsoft;
  vec<int> tmp_score;
  vec<int> flip_time;
  vec<int> tabu_sattime;
  vec<int> arm_n_picks;
  vec<CRef> unSAT;
  vec<Var> unsatSV;
  vec<int> unsatSVidx;
  vec<bool> assignsLS;
  vec<Var> decrVars;
  vec<Var> freeedVars;
  vec<Var> freeedBetterVars;
  int SEED;
  int SEED_FLAG;
  int NOISE;
  int LNOISE;
  int lastAdaptFlip;
  int lastBest;
  int AdaptLength;
  int savedTrailForSattime;
  vec<ClauseLS> clausesLS;
  int maxSattimeTime;
  int nbSattime;
  int maxNbSattime;

  int mark_redundant_clause(int cIndex, vec<int>& involved);
  void attachClauseForSattime(CRef cr);
  void attachClausesForSattime(vec<CRef>& clauses);
  bool satisfiedAtLevel0(CRef cr);
  void clause_value();
  void getNeibors(int v);
  void getNeibors();
  int getVarScore(int v);
  int64_t softScore(int v);
  void updateDelayedReward(vec<Var>& lastArms, int64_t lastLocal,
                           int64_t currentLocal);
  int random_integer(int max);
  void modify_seed();
  void initialize();
  int diversifyForUneven(CRefLS cr, int best_v);
  int my_get_var_to_flip_in_clause(CRefLS cr);
  int my_choose_var_by_random_walk();
  void cleanDecVars(vec<Var>& vs);
  Var cleanDecVarsAndReturnBest(vec<Var>& vs);
  int choose_best_decreasing_var(vec<Var>& vs);
  int choose_decVar();
  void initNoise();
  void adaptNoveltyNoise(int flip);
  void my_satisfy_clauses(Var v, vec<CRefLS>& cs);
  void my_unsatisfy_clauses(Var v, vec<CRefLS>& cs);
  void check_implied_clauses(Var v);
  void clearInClausesLists();
  Var choose_arm(int Nsolutions);
  bool sattime(int maxsteps = 100000000);

  /********************* SAT TIME END ********************************/

  bool betterThan(Var v0, Var v1);
  bool litSatisfiedLS(Lit l);
  void purgeLearnts(vec<CRef>& learnts);

  int64_t cost;

  vec<CRef> resolvents;

  void cancelUntilTrailRecord2(Lit p, int& nbeq, int& nbSoftEq);

  int nbEqUse;
  bool eliminateEqLit(CRef cr, Var v, Var targetV);
  bool eliminateEqLits_(int& debut, bool PBCremoved);
  bool eliminateEqLits();
  bool cleanClause(CRef cr);
  vec<CRef> shortens;
  int64_t optimal;

  /********************* UB/LB Start *********************************/

  /* The initial upper bound from user. */
  int64_t initUB = INT64_MAX;

  /* The initial lower bound from user. */
  int64_t initLB = 0;

  // TODO: explain it.
  int64_t infeasibleUB;

  int64_t objForSearch;

  int64_t solutionCost;

  /* Upper bound of the sum of false soft literals for current search. */
  int64_t UB;

  bool WithNewUB;

  bool feasible;

  /********************** UB/LB End **********************************/

  /********************* SoftLits Start ******************************/

  vec<Lit> softLitsPBorder;

  /* TODO: the difference between allSoftLits. */
  vec<Lit> softLits;

  /* Soft literals represent for unit soft clauses. */
  vec<Lit> unitSoftLits;

  /* Soft literals represent for non-unit soft clauses. */
  vec<Lit> nonUnitSoftLits;

  /* The vector of all the soft literals. There may be some invalid lits in the
   * tail of the vector. */
  vec<Lit> allSoftLits;

  /* The number of soft literals after trim. */
  int nSoftLits;

  /* The minimum weight in 'weights' vector. */
  int64_t minWeight;

  /* The original weights for each soft variable. */
  vec<int64_t> weightsBckp;

  /* The current unlocked weights for each soft variable. */
  vec<int64_t> weights;

  /* The total weights of all failed soft literals by current assignment. */
  int64_t countedWeight;

  /* Record the total weights of all failed soft literals for recovery. */
  int64_t countedWeightRecord;

  /* The total weights of all satisfied soft literals by current assignment. */
  int64_t satisfiedWeight;

  /* Record the initial value of the 'satisfiedWeight' for preprocessing. */
  int64_t initSatisfiedWeight;

  /* Record the total weights of all satisfied soft literals for recovery. */
  int64_t satisfiedWeightRecord;

  /* The total weights of all soft literals. */
  int64_t totalCost;

  /* The total weights of all the soft literals that are fixed to 'False'. */
  int64_t fixedCost;

  /* The total weights of all the soft literals that are fixed to 'True'. */
  int64_t satCost;

  /* The weight of hard clause, equals to 'totalCost' + 1. */
  int64_t hardWeight;

  /* Begin: some statistics about core.  */
  uint64_t numCoresHardConflict = 0;

  uint64_t numCoresFalseVar = 0;

  uint64_t numCoresFalseCore = 0;

  StatisticAverage avgCoreWeight;

  StatisticAverage avgCoreSize;

  /* End: some statistics about core.  */

  /**************************** SoftLits End *************************/

  /********************* Init And Recover Start **********************/

  vec<Lit> savedClauseLits;

  vec<Lit> savedSoftLitsPBorder;

  /* All the soft literals before solving. */
  vec<Lit> savedAllSoftLits;

  vec<Lit> savedEquivLits;

  vec<int64_t> savedWeights;

  vec<char> savedDecision;

  int initNbEliminatedVars;
  int initNbElimclauses;

  int initNbEquivLits;
  int initFeasibleNbEq;
  int initPrevEquivLitsNb;
  int initNbSoftEq;
  int initPrevNbSoftEq;

  vec2<Lit, vec<Lit>> conflictLits;

  int64_t derivedEmptyWeight;

  /********************* Init: *********************/

  void trimSoftLiterals(bool first);
  void trimSoftLiterals2();
  void saveClausesAndSoftLits();
  bool doPreprocessingInInitialization();
  bool doEliminationInInitialization();
  void initStatus();
  void initLookaheadAndCores();
  bool initialization();

  /********************* Recover: *********************/

  void recoverClausesAndSoftLits();
  void recoverEliminatedVariables();
  void clearHardens();
  void recoverEquivlentLits();
  void resetTrailRecordBeginning(int beginning);
  void cancelUntilBeginning(int begnning);

  void updateInfAndSup(int64_t& inf, int64_t& sup);

  /********************* Init And Recover End *********************/

  /********************* Equiv Lits Start *************************/

  vec<Lit> equivLits;
  vec<Lit> rpr;

  int feasibleNbEq;
  int prevEquivLitsNb;
  int nbSoftEq;
  int prevNbSoftEq;

  Lit getRpr(Lit p);
  bool extendEquivLitValue(int debut, bool all);

  /********************* Equiv Lits End ***************************/

  /********************* Inprocessing Elimination Start ***********/

  uint64_t sbsmTtlg, sbsmAbsFail, allsbsm, smeq, s_ticks, ticks, lk_ticks;
  vec<Var> touchedVars;
  vec<bool> touched;
  vec<int> litTrail;
  int nbUnitResolv = 0, nbUnitViviResolv = 0, shortened = 0, nbSimplifing = 0,
      nbRemovedLits = 0, nbAllResolvs = 0;
  int nbLearntResolvs = 0, nb1stClauseSimpL = 0, nbSavedResolvL = 0, sbsmRslv,
      delLitRslv;
  int nbRemovedClausesByElim = 0, nbSavedResolv = 0, nb1stClauseSimp = 0;
  int clause_limit;
  int grow;
  int nbOriClsLits;

  /* Record the trail size after preprocessing. */
  int initTrail;
  int previousTrail;

  uint64_t saved_s_up = 0;

  struct ElimLt {
    const vec<double>& activity;
    explicit ElimLt(const vec<double>& act) : activity(act) {}
    bool operator()(Var x, Var y) const { return activity[x] < activity[y]; }
  };

  vec<double> curr_activity;
  Heap<ElimLt> elim_heap;
  vec<Var> eliminatedVars;
  vec<bool> eliminated;
  vec<uint32_t> elimclauses;
  vec<int> n_occ;
  OccLists<Var, vec<CRef>, ClauseDeleted> occurIn;
  OccLists<Var, vec<CRef>, ClauseDeleted> occurInLocal;

  bool isSubsumed(vec<Lit>& resolvent, bool learnt = false);
  void gatherTouchedClauses();
  bool myAddClause_(vec<Lit>& ps, CRef& cr, int lbd = 0);
  bool addClauseByResolution(vec<Lit>& ps, int lbd = 0);
  static void mkElimClause(vec<uint32_t>& elimclauses, Lit x);
  static void mkElimClause(vec<uint32_t>& elimclauses, Var v, Clause& c);
  void extendModel();
  void removeClauseForElim(CRef cr);
  bool merge(const Clause& _ps, const Clause& _qs, Var v, int& size);
  bool merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause);
  bool cleanClauseAnyWhere(CRef cr);
  void cancelUntilRecord(int record);
  void simpleAnalyzeForElim(CRef confl, vec<Lit>& out_learnt, bool True_confl);
  bool propagateClauseAndAnalyze0(CRef cr, Var v, vec<Lit>& propagatedLits);
  bool propagateClauseAndAnalyze1(CRef cr, Var v, vec<Lit>& propagatedLits,
                                  bool& ttlg);
  bool crossResolvents(vec<CRef>& pos, vec<CRef>& neg, Var v);
  bool crossResolventsL(vec<CRef>& posL, vec<CRef>& negL, Var v);
  void checkOccV(Var v);
  bool eliminateVar(Var v, int& savedTrailSize);
  bool eliminate_();
  void collectOriginalClauses(vec<CRef>& clauseSet);
  void buildElimHeap();
  void collectLocalClauses(vec<CRef>& clauseSet);
  bool eliminate(bool checkOcc = true);
  bool isSubsumed(CRef dr);
  void simplifyLearnt(Clause& c);
  bool simplifyResolvents();
  void checkGarbageForElimVars();
  bool simplesubsumeClauses(CRef cr, int& subsumed, int& deleted_literals);
  bool simplebackwardSubsume_(int& savedTrailSize, bool verbose = true);

  bool isEliminated(Var v);
  void updateElimHeap(Var v);
  Lit simplesubsume(const Clause& c, const Clause& d);

  void purgeClauses(vec<CRef>& cs);
  void simpleAnalyze(CRef confl, vec<Lit>& out_learnt, bool True_confl,
                     bool flysbsmrslv = true);

  /********************* Inprocessing Elimination End *********************/

  /* Keep the soft literals from the cores detected by last lookahead.
   * The literals here will be propagated in the next lookahead.
   */
  vec<Lit> lastAssumed;

  /* For checking errors in debug mode: */
  bool checkHardenheapOrder(int i);
  bool checkClauses(vec<CRef>& cs);

  void printCore(int core_id);
};

/********************* Inprocessing Elimination Start *********************/

inline bool Solver::isEliminated(Var v) { return eliminated[v]; }

inline void Solver::updateElimHeap(Var v) {
  if (elim_heap.inHeap(v)) elim_heap.update(v);
}

inline Lit Solver::simplesubsume(const Clause& c, const Clause& d) {
  allsbsm++;
  if ((c.size() > d.size()) || ((c.abstraction() & ~d.abstraction()) != 0))
    return lit_Error;
  Lit ret = lit_Undef;
  counter++;
  for (int i = 0; i < d.size(); i++) seen2[toInt(d[i])] = counter;

  for (int i = 0; i < c.size(); i++) {
    if (seen2[toInt(~c[i])] == counter) {
      if (ret == lit_Undef)
        ret = c[i];
      else {
        sbsmTtlg++;
        return lit_Error;
      }
    } else if (seen2[toInt(c[i])] != counter) {
      sbsmAbsFail++;
      return lit_Error;
    }
  }
  return ret;
}

/********************* Inprocessing Elimination End *********************/

/********************* Implementation of inline methods: ****************/

inline int Solver::lchild(int i) { return 2 * i + 1; }

inline int Solver::rchild(int i) { return 2 * i + 2; }

inline int Solver::parent(int i) { return (i - 1) / 2; }

inline bool Solver::nthBit(int64_t x, int n) { return (x >> n) & 1; }

inline Lit Solver::mtoCreate(Lit& p) {
  if (p == lit_Undef) p = mkLit(newAuxiVarForPB());
  return p;
}

// For binary clauses, we don't rearrange literals in propagate(), so check and
// make sure the first is an implied lit.
inline void Solver::fixBinClauseOrder(Clause& c) {
  if (c.size() == 2 && value(c[0]) == l_False) {
    assert(value(c[1]) == l_True);
    Lit tmp = c[0];
    c[0] = c[1], c[1] = tmp;
  }
}

inline void Solver::getClauseLits(Clause& c, vec<Lit>& v) {
  v.clear();
  v.growTo(c.size());
  for (int i = 0; i < c.size(); i++) v[i] = c[i];
}

inline void Solver::addPBClause(vec<Lit>& v) {
  assert(v.size() > 1);
  CRef cr = ca.alloc(v, true);
  PBC.push(cr);
  attachClause(cr);
  ca[cr].mark(CORE);
}

inline bool Solver::dynVar(Var v) { return v >= staticNbVars; }

inline bool Solver::isSoftLits(Var v) {
  if (softLits[v] == lit_Undef)
    return false;
  else
    return true;
}

inline bool Solver::isSoftLits(Lit p) { return softLits[var(p)] == p; }

inline void Solver::declareSoftLit(Lit p, bool unit, int64_t weight) {
  Var v = var(p);
  if (unit)
    unitSoftLits.push(p);
  else
    nonUnitSoftLits.push(p);
  ++nSoftLits;
  assert(toInt(p) >= 0);
  softLits[v] = p;
  activityLB[v] = 0;
  weights[v] = weight;
  orderHeapLookahead.insert(var(p));
}

inline void Solver::removeSoftLit(Lit p) {
  softLits[var(p)] = lit_Undef;
  --nSoftLits;
  weights[var(p)] = 0;
  weightsBckp[var(p)] = 0;
  hardened[var(p)] = false;
}

inline CRef Solver::reason(Var x) const { return vardata[x].reason; }
inline int Solver::level(Var x) const { return vardata[x].level; }
inline int Solver::trailIndex(Var x) const { return vardata[x].index; }

inline void Solver::insertVarOrder(Var x) {
  Heap<VarOrderLt>& order_heap = VSIDS ? order_heap_VSIDS : order_heap_CHB;
  if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x);
}

inline void Solver::varDecayActivity() { var_inc *= (1 / var_decay); }

inline void Solver::varBumpActivity(Var v, double mult) {
  if ((activity_VSIDS[v] += var_inc * mult) > 1e100) {
    // Rescale:
    for (int i = 0; i < nVars(); i++) activity_VSIDS[i] *= 1e-100;
    var_inc *= 1e-100;
  }

  // Update order_heap with respect to new activity:
  if (order_heap_VSIDS.inHeap(v)) order_heap_VSIDS.decrease(v);
}

inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }

inline void Solver::claBumpActivity(Clause& c) {
  if ((c.activity() += cla_inc) > 1e20) {
    // Rescale:
    for (int i = 0; i < learnts_local.size(); i++)
      ca[learnts_local[i]].activity() *= 1e-20;

    for (int i = 0; i < learnts_core.size(); i++)
      ca[learnts_core[i]].activity() *= 1e-20;

    for (int i = 0; i < learnts_tier2.size(); i++)
      ca[learnts_tier2[i]].activity() *= 1e-20;

    for (int i = 0; i < PBC.size(); i++) ca[PBC[i]].activity() *= 1e-20;

    for (int i = 0; i < isetClauses.size(); i++)
      ca[isetClauses[i]].activity() *= 1e-20;

    cla_inc *= 1e-20;
  }
}

inline void Solver::checkGarbage(void) {
  if (toGarbageCollect()) garbageCollect();
}

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool Solver::enqueue(Lit p, CRef from) {
  return value(p) != l_Undef ? value(p) != l_False
                             : (uncheckedEnqueue(p, from), true);
}
inline bool Solver::addClause(const vec<Lit>& ps) {
  ps.copyTo(add_tmp);
  return addClause_(add_tmp);
}
inline bool Solver::addEmptyClause() {
  add_tmp.clear();
  return addClause_(add_tmp);
}
inline bool Solver::addClause(Lit p) {
  add_tmp.clear();
  add_tmp.push(p);
  return addClause_(add_tmp);
}
inline bool Solver::addClause(Lit p, Lit q) {
  add_tmp.clear();
  add_tmp.push(p);
  add_tmp.push(q);
  return addClause_(add_tmp);
}
inline bool Solver::addClause(Lit p, Lit q, Lit r) {
  add_tmp.clear();
  add_tmp.push(p);
  add_tmp.push(q);
  add_tmp.push(r);
  return addClause_(add_tmp);
}
inline bool Solver::locked(const Clause& c) const {
  int i = c.size() != 2 ? 0 : (value(c[0]) == l_True ? 0 : 1);
  return value(c[i]) == l_True && reason(var(c[i])) != CRef_Undef &&
         ca.lea(reason(var(c[i]))) == &c;
}
inline void Solver::newDecisionLevel() {
  trail_lim.push(trail.size());
  falseLits_lim.push(falseLits.size());
  countedWeight_lim.push(countedWeight);
  satisfiedWeight_lim.push(satisfiedWeight);
  hardens_lim.push(hardens.size());
}

inline int Solver::decisionLevel() const { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel(Var x) const {
  return 1 << (level(x) & 31);
}
inline lbool Solver::value(Var x) const { return assigns[x]; }
inline lbool Solver::value(Lit p) const { return assigns[var(p)] ^ sign(p); }
inline lbool Solver::modelValue(Var x) const { return model[x]; }
inline lbool Solver::modelValue(Lit p) const { return model[var(p)] ^ sign(p); }
inline int Solver::nAssigns() const { return trail.size(); }
inline int Solver::nClauses() const { return clauses.size(); }
inline int Solver::nLearnts() const {
  return learnts_core.size() + learnts_tier2.size() + learnts_local.size();
}
inline int Solver::nVars() const { return vardata.size(); }
inline int Solver::nFreeVars() const {
  return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]);
}
inline void Solver::setPolarity(Var v, bool b) { polarity[v] = b; }

inline void Solver::setDecisionVar(Var v, bool b) {
  if (b && !decision[v]) {
    dec_vars++;  // Set decision variable.
  } else if (!b && decision[v]) {
    dec_vars--;  // Unset decision variable.
  }

  decision[v] = b;
  if (b) {
    if (!order_heap_CHB.inHeap(v)) {
      order_heap_CHB.insert(v);
    }
    if (!order_heap_VSIDS.inHeap(v)) {
      order_heap_VSIDS.insert(v);
    }
  }
}

inline void Solver::setConfBudget(int64_t x) {
  conflict_budget = conflicts + x;
}

inline void Solver::setPropBudget(int64_t x) {
  propagation_budget = propagations + x;
}

inline void Solver::interrupt() { asynch_interrupt = true; }
inline void Solver::clearInterrupt() { asynch_interrupt = false; }
inline void Solver::budgetOff() { conflict_budget = propagation_budget = -1; }
inline bool Solver::withinBudget() const {
  return !asynch_interrupt &&
         (conflict_budget < 0 || conflicts < (uint64_t)conflict_budget) &&
         (propagation_budget < 0 ||
          propagations < (uint64_t)propagation_budget);
}

// FIXME: after the introduction of asynchronous interrruptions the
// solve-versions that return a pure bool do not give a safe interface. Either
// interrupts must be possible to turn off here, or all calls to solve must
// return an 'lbool'. I'm not yet sure which I prefer.
inline bool Solver::solve() {
  budgetOff();
  assumptions.clear();
  return solve_() == l_True;
}

inline bool Solver::solve(Lit p) {
  budgetOff();
  assumptions.clear();
  assumptions.push(p);
  return solve_() == l_True;
}

inline bool Solver::solve(Lit p, Lit q) {
  budgetOff();
  assumptions.clear();
  assumptions.push(p);
  assumptions.push(q);
  return solve_() == l_True;
}

inline bool Solver::solve(Lit p, Lit q, Lit r) {
  budgetOff();
  assumptions.clear();
  assumptions.push(p);
  assumptions.push(q);
  assumptions.push(r);
  return solve_() == l_True;
}

inline bool Solver::solve(const vec<Lit>& assumps) {
  budgetOff();
  assumps.copyTo(assumptions);
  return solve_() == l_True;
}

inline lbool Solver::solveLimited(const vec<Lit>& assumps) {
  assumps.copyTo(assumptions);
  return solve_();
}

inline bool Solver::okay() const { return ok; }

inline void Solver::toDimacs(const char* file) {
  vec<Lit> as;
  toDimacs(file, as);
}

inline void Solver::toDimacs(const char* file, Lit p) {
  vec<Lit> as;
  as.push(p);
  toDimacs(file, as);
}

inline void Solver::toDimacs(const char* file, Lit p, Lit q) {
  vec<Lit> as;
  as.push(p);
  as.push(q);
  toDimacs(file, as);
}

inline void Solver::toDimacs(const char* file, Lit p, Lit q, Lit r) {
  vec<Lit> as;
  as.push(p);
  as.push(q);
  as.push(r);
  toDimacs(file, as);
}

}  // namespace Minisat

#endif

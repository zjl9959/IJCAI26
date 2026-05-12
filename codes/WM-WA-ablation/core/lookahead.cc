#include "PrintFlags.h"
#include "Solver.h"
#include "mtl/Sort.h"
#include "utils/System.h"

void Solver::cancelUntilTrailRecordFillHeap() {
  for (int i = trailRecord; i < trail.size(); i++) {
    Var v = var(trail[i]);
    assigns[v] = l_Undef;
    if (isSoftLits(v)) {
      activityLB[v] = (1 - stepSizeLB) * activityLB[v];
      insertSoftLitOrder(v);
      orderHeapLookahead.decrease(v);
    }
  }
  qhead = trailRecord;
  resetTrailRecord();
}

Var Solver::pickLookaheadVar() {
  Var v = var_Undef;
  while (!lastConflLits.empty()) {
    v = lastConflLits.removeMin();
    assert(v != var_Undef);
    if (weights[v] > 0) assert(isSoftLits(v));
    if (value(v) == l_Undef && weights[v] > 0) return v;
  }
  while (!orderHeapLookahead.empty()) {
    v = orderHeapLookahead.removeMin();
    assert(v != var_Undef);
    if (weights[v] > 0) assert(isSoftLits(v));
    if (value(v) == l_Undef && weights[v] > 0) return v;
  }
  return var_Undef;
}

bool Solver::enqueueAssumptions(int &nextIdx, bool recheckNext) {
  bool someEnqueued = false;
  if (recheckNext) {
    while (nextIdx < lastCores.size() && !someEnqueued) {
      int core = lastCores[nextIdx];
      LocalCore &c = localCores[core];
      bool active = true;
      for (int j = 0; j < c.coreLits.size() && active; j++) {
        Lit p = c.coreLits[j].lit;
        if (value(p) == l_False) active = false;
      }
      if (active) {
        for (int j = 0; j < c.coreLits.size(); j++) {
          Lit p = c.coreLits[j].lit;
          Var v = var(p);
          if (value(v) == l_Undef && weights[v] > 0) {
            uncheckedEnqueueForLK(p);
            someEnqueued = true;
          }
        }
      } else {
        for (int j = 0; j < c.coreLits.size(); j++) {
          if (value(c.coreLits[j].lit) == l_Undef &&
              weights[var(c.coreLits[j].lit)] > 0) {
            lastConflLits.update(var(c.coreLits[j].lit));
          }
        }
      }

      nextIdx++;
    }

    if (someEnqueued) return true;
    if (activeCores.size() > 0) {
      vec<coreLit> &coreLits = localCores[activeCores.last()].coreLits;
      for (int i = coreLits.size() - 1; i >= 0; i--) {
        if (nonLockedVar(var(coreLits[i].lit)) &&
            value(coreLits[i].lit) == l_Undef) {
          uncheckedEnqueueForLK(coreLits[i].lit);
          someEnqueued = true;
        }
      }
    }
  }

  if (someEnqueued) return true;

  Var v = pickLookaheadVar();
  if (v == var_Undef) return false;

  assert(nonLockedVar(v));
  uncheckedEnqueueForLK(softLits[v]);
  return true;
}

void Solver::moreLookahead() {
  resetCoresData();
  vec<Lit> out_learnt;
  softConflictFlag = false;
  clearFalseVar();
  clearFalseCores();
  // Recheck next when there is a conflict or falseVar found.
  bool recheckNext = true;
  bool maxResDone = false;
  int nextIdx = 0;

  // Update trailIndexLimitDelta = (lk_propagations / coresNum) * factor
  if (avgCoreSize.count() > 100) {
    trailIndexLimitDelta = (lk_propagations / avgCoreSize.count()) * 0.6;
  }

  while (countedWeight + lookaheadConflictCost < UB) {
    if (!enqueueAssumptions(nextIdx, recheckNext)) {
      TodoSecondLookahead = todoSecondLookahead();
      cancelUntilTrailRecordFillHeap();
      break;
    }
    recheckNext = false;

    CRef confl = propagateForLK();
    if (confl != CRef_Undef || falseVar != var_Undef) {
      assert(falseVar == var_Undef || reason(falseVar) != CRef_Undef);
      if (confl == CRef_Undef) {
        confl = reason(falseVar);
        numCoresFalseVar++;
      } else {
        // Hard conflict has higher priority than falseVar.
        clearFalseVar();
        numCoresHardConflict++;
      }

      int coreIdx = pickCoreIdx();
      int64_t coreCost;
      lookbackResetTrail(confl, falseVar, out_learnt, coreIdx, coreCost,
                         maxResDone,
                         UB - countedWeight - lookaheadConflictCost);
      assert(coreCost > 0);
      falseVar = var_Undef;
      recheckNext = true;
      LocalCore &core = localCores[coreIdx];

      // This case is triggered when it is discovered that a literal can be
      // propagated at DL, because only  assigning ~out_learnt[0] suffices to
      // derive a conflicting clause
      if (core.coreLits.size() == 0) {
        freeCores.push(coreIdx);
        resetConflicts_();
        int prevLevel = decisionLevel();
        fixByLookahead(out_learnt);
        CRef confl = lPropagate();
        if (confl != CRef_Undef || softConflictFlag) {
          if (confl != CRef_Undef) {
            LHconfl = confl;
            softConflictFlag = false;
          }
          return;
        }
        setTrailRecord();
        assert(UB > countedWeight);
        assert(lookaheadConflictCost == 0);
        assert(activeCores.size() == 0);
        lastConflLits.clear();
        maxResDone = false;
        nextIdx = 0;
        if (prevLevel > decisionLevel()) return;
      } else {
        setCore(coreIdx, coreCost);
      }
    }
  }
  if (countedWeight + lookaheadConflictCost >= UB) {
    assert(LHconfl == CRef_Undef);
    softConflictFlag = true;
    nbLKsuccess++;
  }
}

bool Solver::uncheckedEnqueueForLKMultilocks(Lit p, CRef from) {
  assert(value(p) == l_Undef);
  // Assign a value to the variable of the soft literal 'p':
  LAM_PRINT(LOOKAHEAD, "  propagate %s reason %d\n", lit2str(p), from);
  Var v = var(p);
  assigns[v] = lbool(!sign(p));
  vardata[v].reason = from;
  vardata[v].level = decisionLevel() + 1;
  vardata[v].index = trail.size();
  trail.push_(p);

  // Handle the unlock logical:
  if (isSoftLits(v)) {
    if (from == CRef_Undef) {
      assert(softLits[v] == p);  // This is a decision.
    } else if (softLits[v] == ~p) {
      /* Here, 'p' is a falsed soft literal, then try to unlock all the cores
       * related to it.*/
      LAM_PRINT(LOOKAHEAD, "  c falsified softLit %d \n", toInt(p));
      if (weights[v] > 0) {
        /* The reason of 'p'=false is the propagation of other literals. So we
         * need to learn a new core later. */
        LAM_PRINT(LOOKAHEAD, "    c find falseVar %d, lit %d, \n", v,
                  toInt(softLits[v]));
        if (weights[v] >= falseVarWeight) {
          if (falseVar == var_Undef && allFalseCores.size() == 0) {
            // Set the limit when the first falseVar is found.
            trailIndexLimit = trail.size() + trailIndexLimitDelta;
          }
          falseVarWeight = weights[v];
          falseVar = v;
        }
      } else {
        /* Here, 'p' appears in some cores. */
        assert(coresOfVar[v].size() > 0 && weights[v] == 0);
        // s1:5 c1(s1:1, s2:3) c2(s1:2, s3:2) c3:(s1:2, s4:1)
        for (int i = 0; i < coresOfVar[v].size(); i++) {
          int coreid = coresOfVar[v][i];
          assert(coreid >= 0 && coreid < localCores.size());
          LocalCore &core = localCores[coreid];
          // assert(core.falsifiedWeight <= core.weight);

          int64_t w = getCorelitWeight(coreid, v);
          assert(w > 0);
          /* 'falsifiedWeight == 0' means the status of this core is changed at
           * the first time. */
          if (core.falsifiedWeight == 0) {
            affectedCores.push(coreid);
          }
          core.falsifiedWeight += w;
          LAM_PRINT(LOOKAHEAD,
                    "    c core %d falsifiedWeight inc to %" PRId64
                    ", core weight %" PRId64 " \n",
                    coreid, core.falsifiedWeight, core.weight);
          /* The core still can not be unlocked. */
          if (core.falsifiedWeight < core.weight) continue;
          if (core.unlockedIndex == -1) {
            // The core can be unlocked here.
            core.unlockedIndex = trail.size();
            for (int j = 0; j < core.coreLits.size(); j++) {
              /* Look through all the literals of the core, and unlock all the
               * unlocked literals. */
              Lit pp = core.coreLits[j].lit;
              Var vv = var(pp);
              if (unlockCoreOfVar[vv] == -1) {
                unlockCoreOfVar[vv] = coreid;
                unlockedVars.push(vv);
              }
              if (value(pp) == l_Undef) insertSoftLitOrder(vv);
            }
          }
          assert(core.falsifiedWeight >= core.weight);

          if (core.falsifiedWeight > core.weight) {
            /* Here, we found a new core! */
            LAM_PRINT(LOOKAHEAD, "    c find falseCore %d \n", coreid);
            if (falseVar == var_Undef && allFalseCores.size() == 0) {
              // Set the limit when the first falseVar is found.
              trailIndexLimit = trail.size() + trailIndexLimitDelta;
            }
            allFalseCores.insert(coreid);
          }
        }
      }
    }
  }
  return (falseVar != var_Undef || allFalseCores.size() > 0) &&
         trail.size() >= trailIndexLimit;
}

CRef Solver::propagateForLKMultilocks() {
  clearFalseVar();
  clearFalseCores();
  CRef confl = CRef_Undef;
  int num_props = 0;
  watches.cleanAll();
  watches_bin.cleanAll();
  while (qhead < trail.size()) {
    Lit p = trail[qhead++];  // 'p' is enqueued fact to propagate.
    vec<Watcher> &ws = watches[p];
    Watcher *i, *j, *end;
    num_props++;
    // First, Propagate binary clauses
    vec<Watcher> &wbin = watches_bin[p];

    for (int k = 0; k < wbin.size(); k++) {
      Lit imp = wbin[k].blocker;
      if (value(imp) == l_False) {
        binConfl[0] = ~p;
        binConfl[1] = imp;
        return CRef_Bin;
      }
      if (value(imp) == l_Undef) {
        if (uncheckedEnqueueForLKMultilocks(imp, wbin[k].cref)) {
          return CRef_Undef;
        }
      }
    }
    for (i = j = (Watcher *)ws, end = i + ws.size(); i != end;) {
      // Try to avoid inspecting the clause:
      Lit blocker = i->blocker;
      if (value(blocker) == l_True) {
        *j++ = *i++;
        continue;
      }
      // Make sure the false literal is data[1]:
      CRef cr = i->cref;
      Clause &c = ca[cr];
      Lit false_lit = ~p;
      if (c[0] == false_lit) c[0] = c[1], c[1] = false_lit;
      assert(c[1] == false_lit);
      // If 0th watch is true, then clause is already satisfied.
      // However, 0th watch is not the blocker, make it blocker using a new
      // watcher w why not simply do i->blocker=first in this case?
      Lit first = c[0];
      //  Watcher w     = Watcher(cr, first);
      if (first != blocker && value(first) == l_True) {
        i->blocker = first;
        *j++ = *i++;
        continue;
      }
      assert(c.lastPoint() >= 2);
      if (c.lastPoint() > c.size()) c.setLastPoint(2);
      for (int k = c.lastPoint(); k < c.size(); k++) {
        if (value(c[k]) == l_Undef) {
          // watcher i is abandonned using i++, because cr watches now ~c[k]
          // instead of p the blocker is first in the watcher. However, the
          // blocker in the corresponding watcher in ~first is not c[1]
          Watcher w = Watcher(cr, first);
          i++;
          c[1] = c[k];
          c[k] = false_lit;
          watches[~c[1]].push(w);
          c.setLastPoint(k + 1);
          goto NextClause;
        } else if (value(c[k]) == l_True) {
          i->blocker = c[k];
          *j++ = *i++;
          c.setLastPoint(k);
          goto NextClause;
        }
      }
      for (int k = 2; k < c.lastPoint(); k++) {
        if (value(c[k]) == l_Undef) {
          // watcher i is abandonned using i++, because cr watches now ~c[k]
          // instead of p the blocker is first in the watcher. However, the
          // blocker in the corresponding watcher in ~first is not c[1]
          Watcher w = Watcher(cr, first);
          i++;
          c[1] = c[k];
          c[k] = false_lit;
          watches[~c[1]].push(w);
          c.setLastPoint(k + 1);
          goto NextClause;
        } else if (value(c[k]) == l_True) {
          i->blocker = c[k];
          *j++ = *i++;
          c.setLastPoint(k);
          goto NextClause;
        }
      }
      // Did not find watch -- clause is unit under assignment:
      i->blocker = first;
      *j++ = *i++;
      if (value(first) == l_False) {
        confl = cr;
        qhead = trail.size();
        // Copy the remaining watches:
        while (i < end) *j++ = *i++;
      } else {
        if (uncheckedEnqueueForLKMultilocks(first, cr)) {
          qhead = trail.size();
          // Copy the remaining watches:
          while (i < end) *j++ = *i++;
        }
      }
    NextClause:;
    }
    ws.shrink(i - j);
  }
  lk_propagations += num_props;
  return confl;
}

Var Solver::pickSecondLookaheadVar() {
  Var v = var_Undef;
  while (!lastConflLits.empty()) {
    v = lastConflLits.removeMin();
    assert(v != var_Undef);
    if (value(v) == l_Undef && (nonLockedVar(v) || unlockedVar(v))) return v;
  }
  while (!orderHeapLookahead.empty()) {
    v = orderHeapLookahead.removeMin();
    assert(v != var_Undef);
    if (value(v) == l_Undef && (nonLockedVar(v) || unlockedVar(v))) return v;
  }
  return var_Undef;
}

// Pick a soft literal to enqueue as an assumption
bool Solver::enqueueAssumptionsMultilocks(vec<Lit> &allAssumed) {
  while (lastAssumed.size() > 0) {
    Var v = var(lastAssumed.last());
    lastAssumed.pop();
    if (value(v) == l_Undef && (nonLockedVar(v) || unlockedVar(v))) {
      uncheckedEnqueueForLKMultilocks(softLits[v]);
      allAssumed.push(softLits[v]);
      return true;
    }
  }

  Var v = pickSecondLookaheadVar();
  if (v == var_Undef) return false;
  assert(nonLockedVar(v) || unlockedVar(v));
  uncheckedEnqueueForLKMultilocks(softLits[v]);
  allAssumed.push(softLits[v]);
  return true;
}

int Solver::seeUnlockLits(Var x, int falseVar) {
  int nbfalse = 0;
  int subcoreid = unlockCoreOfVar[x];
  LocalCore &subcore = localCores[subcoreid];

  assert(subcore.falsifiedWeight >= subcore.weight);
  if (subcore.seen == true) {
    LAM_PRINT(LOOKAHEAD, "    Var %d, softLit %d, core %d already marked.\n", x,
              toInt(softLits[x]), subcoreid);
    return 0;
  }

  subcore.seen = true;
  LAM_PRINT(LOOKAHEAD, "    in seeUnlockLits, add core %d as subcore: \n",
            subcoreid);
  for (int i = 0; i < subcore.coreLits.size(); i++) {
    Var v = var(subcore.coreLits[i].lit);
    assert(level(v) > decisionLevel());
    if (v == falseVar || v == x) continue;
    if (!seen[v] && value(subcore.coreLits[i].lit) == l_False &&
        trailIndex(v) <= trailIndex(x)) {
      nbfalse++;
      seen[v] = 1;
    }
  }

  subCores.push(subcoreid);
  return nbfalse;
}

int Solver::analyzeWithClauseBin() {
  assert(level(var(binConfl[0])) > decisionLevel());
  assert(level(var(binConfl[1])) > decisionLevel());
  seen[var(binConfl[0])] = 1;
  seen[var(binConfl[1])] = 1;
  if (VSIDS) {
    varBumpActivity(var(binConfl[0]), .1);
    varBumpActivity(var(binConfl[0]), .1);
  }
  return 2;
}

int Solver::analyzeWithClause(CRef confl, vec<Lit> &out_learnt, int start) {
  int res = 0;
  Clause &c = ca[confl];
  for (int i = start; i < c.size(); i++) {
    Lit q = c[i];
    Var v = var(q);
    if (level(v) > 0) {
      if (!seen[v]) {
        seen[v] = 1;
        if (level(v) > decisionLevel())
          res++;
        else {
          // Note that involvedLits can contain lits from other isets
          // This is not the case for out_learnt
          out_learnt.push(q);
          newcoreReason.push(q);
        }
        if (VSIDS) varBumpActivity(v, .1);
      }
    }
  }
  return res;
}

void Solver::analyzeWithConfl(CRef confl, int &pathC, vec<Lit> &out_learnt) {
  if (confl == CRef_Bin)
    pathC += analyzeWithClauseBin();
  else
    pathC += analyzeWithClause(confl, out_learnt, 0);
}

void Solver::analyzeWithFalsevar(int &pathC, vec<Lit> &out_learnt) {
  newcoreLits.push(coreLit(softLits[falseVar], weights[falseVar]));
  keyAssignment.push(softLits[falseVar]);
  CRef confl = reason(falseVar);
  Clause &c = ca[confl];
  fixBinClauseOrder(c);
  if (weights[falseVar] == 0) pathC += seeUnlockLits(falseVar, falseVar);
  assert(level(falseVar) > decisionLevel());
  out_learnt.push(softLits[falseVar]);
  pathC += analyzeWithClause(confl, out_learnt, 1);
}

void Solver::analyzeWithFalsecore(int &pathC, vec<Lit> &out_learnt) {
  LocalCore &core = localCores[falseCore];
  assert(!core.seen && core.falsifiedWeight > core.weight);
  core.seen = true;
  for (int i = 0; i < core.coreLits.size(); i++) {
    Var v = var(core.coreLits[i].lit);
    assert(level(v) > decisionLevel());
    if (weights[v] == 0 && value(core.coreLits[i].lit) == l_False) {
      newcoreLits.push(coreLit(core.coreLits[i].lit, weights[v]));
      out_learnt.push(core.coreLits[i].lit);
    }
  }
  subCores.push(falseCore);

  CRef confl = CRef_Undef;
  for (int i = 0; i < core.coreLits.size(); i++) {
    Lit p = core.coreLits[i].lit;
    Var v = var(p);
    if (value(p) == l_False && weights[v] == 0) {
      assert(core.coreLits[i].weight > 0);
      confl = reason(v);
      Clause &c = ca[confl];
      fixBinClauseOrder(c);
      pathC += analyzeWithClause(confl, out_learnt, 1);
    }
  }
}

void Solver::lookbackResetTrailMultilocks(CRef confl, vec<Lit> &out_learnt,
                                          bool resDone, int64_t remainingCost) {
  lastAssumed.clear();
  int pathC = 0;
  out_learnt.clear();
  out_learnt.push();
  resDone = true;

  keyAssignment.clear();
  newcoreReason.clear();
  newcoreLits.clear();

  if (confl != CRef_Undef) {
    numCoresHardConflict++;
    analyzeWithConfl(confl, pathC, out_learnt);
  } else if (falseVar != var_Undef) {
    numCoresFalseVar++;
    analyzeWithFalsevar(pathC, out_learnt);
  } else {
    numCoresFalseCore++;
    analyzeWithFalsecore(pathC, out_learnt);
  }

  int index = trail.size() - 1;
  while (index >= trailRecord) {
    Lit p = trail[index--];
    Var v = var(p);
    if (seen[v]) {
      seen[v] = 0;
      pathC--;
      confl = reason(v);

      // We will need to keep this decrease only if confl==CRef_Undef,
      //   unless we enter the following special case, where it is accepted to
      //   use a propagated softLit (i.e. confl!=CRef_Undef) for the core in
      //   replacement

      // If UIP is reached: pathC==0.
      // And the core is empty until now: localCores[nbIsets].size() == 0
      // And
      //       is not the last iset (i.e. the one triggering the soft conflict):
      //       minIsetCost < remainingCost or the recently visited lit is soft,
      //       and therefore the unique soft lit to be included in the iset

      if (pathC == 0 && newcoreLits.size() == 0) {
        out_learnt[0] = ~p;
        // assigns[v] = l_Undef;
        //  If creating the unit iset will trigger the soft conflict, do it.
        //   This branch can be seen as a premature exit of the loop, since we
        //   already know that pathC==0
        //  Otherwise, we exit with an empty iset and p will be propagated by
        //  fixByLookahead Note that here p is not necessarily a manually
        //  assigned softLit for LA but can be a propagated one.
        //    In this case it acts in replacement and takes it place in the iset

        if ((nonLockedVar(v) || unlockedVar(v)) &&
            weights[v] >= remainingCost) {
          keyAssignment.push(p);
          newcoreLits.push(coreLit(p, weights[v]));
        }

        if (isSoftLits(v)) insertSoftLitOrder(v);
        break;
      }
      if (confl == CRef_Undef) {  // Propagated soft literal for LA
        assert(nonLockedVar(v) || unlockedVar(v));
        out_learnt.push(~p);
        keyAssignment.push(p);
        newcoreLits.push(coreLit(p, weights[v]));
        LAM_PRINT(LOOKAHEAD, "c add positive assignment var %d, lit %d \n", v,
                  toInt(p));
        if (weights[v] == 0)
          pathC += seeUnlockLits(v, falseVar);
        else
          lastAssumed.push(p);
      } else {
        // Undo the minimum for a softLit p s.t. reason(p)!=CRef_Undef, and
        // therefore is not put in isets
        Clause &rc = ca[confl];
        if (!isSoftLits(v) || !hardened[v]) fixBinClauseOrder(rc);
        int nbSeen = 0;
        int resolventSize = pathC + out_learnt.size();
        for (int j = 1; j < rc.size(); j++) {
          Lit q = rc[j];
          Var vv = var(q);
          if (level(vv) > 0) {
            if (seen[vv])
              nbSeen++;
            else {
              seen[vv] = 1;
              if (level(vv) > decisionLevel())
                pathC++;
              else {
                out_learnt.push(q);
                newcoreReason.push(q);
              }
              if (VSIDS) varBumpActivity(vv, .1);
            }
          }
        }
        if (!resDone && nbSeen >= resolventSize) {
          assert(falseVar == var_Undef);
          reduceClause(confl, pathC);
        }
      }
    } else if (nonLockedVar(v) || unlockedVar(v))
      insertSoftLitOrder(v);
  }
  for (int i = 0; i < newcoreReason.size(); i++)
    seen[var(newcoreReason[i])] = 0;
}

// 在做完不解锁的 lookahead后，判断是否需要做加锁的 lookahead。
bool Solver::todoSecondLookahead() {
  if (activeCores.size() == 0) {
    LOOKAHEAD_MULTILOCKS_SKIP++;
    return false;
  }

  bool res = false;
  int falseLitIndex = falseLitsRecord;
  CRef confl = CRef_Undef;
  while (falseLitIndex < falseLits.size() && !res) {
    Lit p = falseLits[falseLitIndex++];
    assert(value(p) == l_False);
    Var v = var(p);
    for (int i = 0; i < coresOfVar[v].size() && !res; i++) {
      LocalCore &core = localCores[coresOfVar[v][i]];
      core.falsifiedWeight = 0;
      for (int j = 0; j < core.coreLits.size(); j++) {
        if (value(core.coreLits[j].lit) == l_Undef)
          uncheckedEnqueueForLK(core.coreLits[j].lit);
        else if (value(core.coreLits[j].lit) == l_False)
          core.falsifiedWeight += core.coreLits[j].weight;
      }
      if (core.falsifiedWeight > core.weight) res = true;
      core.falsifiedWeight = 0;
    }
    if (!res) {
      confl = propagateForLK();
      if (confl != CRef_Undef || falseVar != var_Undef) res = true;
    }
  }

  if (!res) {
    LOOKAHEAD_MULTILOCKS_SKIP++;
    return false;
  }

  return true;
}

void Solver::lookaheadMultilocks() {
  vec<Lit> out_learnt;
  setTrailRecord();
  softConflictFlag = false;
  clearFalseVar();
  clearFalseCores();
  bool maxResDone = false;
  assert(unlockedVars.size() == 0);

  lastAssumed.clear();
  vec<Lit> allAssumed;  // Temporary vec to contain propagated literals for
                        // lastAssumed.
  allAssumed.clear();

  double startTime = cpuTime();

  while (countedWeight + lookaheadConflictCost < UB) {
    if (!enqueueAssumptionsMultilocks(allAssumed)) {
      // Stop lookahead because all the soft literals are propagated.
      cancelUntilTrailRecordFillHeap();
      recoverAffectedCoresAfterLookahead(-1);
      break;
    }

    CRef confl = propagateForLKMultilocks();
    if (confl != CRef_Undef || falseVar != var_Undef ||
        allFalseCores.size() > 0) {
      assert(falseVar == var_Undef || reason(falseVar) != CRef_Undef ||
             allFalseCores.size() > 0);

      if (confl != CRef_Undef) {
        // Hard conflict has higher priority than falseVar.
        clearFalseVar();
        clearFalseCores();
        numCoresHardConflict++;
      } else {
        // Decide the falseCore with the highest initial weight.
        falseCoreInitWeight = 0;
        for (auto coreid : allFalseCores) {
          int64_t init_weight = getFalseCoreInitialWeight(coreid);
          if (init_weight > falseCoreInitWeight) {
            falseCoreInitWeight = init_weight;
            falseCore = coreid;
          }
        }
        // Choose between falseVar and falseCore.
        if (falseCoreInitWeight > falseVarWeight) {
          assert(falseCore != core_Undef);
          clearFalseVar();
          numCoresFalseCore++;
        } else {
          assert(falseVar != var_Undef);
          clearFalseCores();
          numCoresFalseVar++;
        }
      }

      int coreid = pickCoreIdx();
      lookbackResetTrailMultilocks(confl, out_learnt, maxResDone,
                                   UB - countedWeight - lookaheadConflictCost);
      if (newcoreLits.size() > 0) {
        setCoreMultilock(coreid);
        counter++;
        for (int i = 0; i < lastAssumed.size(); i++) {
          if (weights[var(lastAssumed[i])] == 0)
            lastAssumed.clear();
          else
            seen2[var(lastAssumed[i])] = counter;
        }
        if (lastAssumed.size() > 0) {
          lastAssumed.clear();
          for (int i = allAssumed.size() - 1; i >= 0; i--)
            if (seen2[var(allAssumed[i])] == counter)
              lastAssumed.push(allAssumed[i]);
        }
        allAssumed.clear();
        cancelUntilTrailRecordUnsee();
        clearFalseVar();
        clearFalseCores();
      } else {
        cancelUntilTrailRecordUnsee();
        clearFalseVar();
        clearFalseCores();
        freeCores.push(coreid);
        resetConflicts_();
        allAssumed.clear();
        lastAssumed.clear();
        int prevLevel = decisionLevel();
        fixByLookahead(out_learnt);
        CRef confl = lPropagate();
        if (confl != CRef_Undef || softConflictFlag) {
          if (confl != CRef_Undef) {
            LHconfl = confl;
            softConflictFlag = false;
          }
          double endTime = cpuTime();
          SECOND_LOOKAHEAD_TIME += (endTime - startTime);
          return;
        }
        setTrailRecord();
        assert(UB > countedWeight);
        assert(lookaheadConflictCost == 0);
        assert(activeCores.size() == 0);
        lastConflLits.clear();
        maxResDone = false;
        double endTime = cpuTime();
        SECOND_LOOKAHEAD_TIME += (endTime - startTime);
        if (prevLevel == decisionLevel()) redoLookahead = true;
        return;
      }
    }
  }

  double endTime = cpuTime();
  SECOND_LOOKAHEAD_TIME += (endTime - startTime);

  if (countedWeight + lookaheadConflictCost >= UB) {
    LOOKAHEAD_MULTILOCKS_SUCCS++;
    assert(LHconfl == CRef_Undef);
    softConflictFlag = true;
  }
}

void Solver::printAroundSecondLookahead(bool before) {
  if (before)
    LAM_PRINT(LOOKAHEAD, "\n ***** Lookahead %" PRIu64 " ***** \n", LOOKAHEAD);
  else
    LAM_PRINT(LOOKAHEAD,
              "\n ***** Lookahead Multilocks %" PRIu64 " End ***** \n",
              LOOKAHEAD_MULTILOCKS);

  LAM_PRINT(LOOKAHEAD,
            "c UB=%" PRId64 ", laConflictCost=%" PRId64
            ", countedWeight=%" PRId64 ", rest=%" PRId64 "\n",
            UB, lookaheadConflictCost, countedWeight,
            UB - lookaheadConflictCost - countedWeight);
  for (int i = 0; i < activeCores.size(); i++) {
    LocalCore &core = localCores[activeCores[i]];
    LAM_PRINT(LOOKAHEAD,
              "core id %d, weight %" PRId64 ", level %d: ", activeCores[i],
              core.weight, core.level);
    for (int j = 0; j < core.coreLits.size(); j++) {
      assert(value(core.coreLits[j].lit) == l_Undef);
      LAM_PRINT(LOOKAHEAD, "%d(%" PRId64 "),", toInt(core.coreLits[j].lit),
                core.coreLits[j].weight);
    }
    LAM_PRINT(LOOKAHEAD, "\n");
  }
  LAM_PRINT(LOOKAHEAD, "\n");
}

void Solver::todoLookahead() {
  bool first = true;
  while (true) {
    moreLookahead();  // This is the default lookahead.
    if (TodoSecondLookahead) {
      printAroundSecondLookahead(true);
      if (first) {
        LOOKAHEAD_MULTILOCKS++;
        first = false;
      }
      redoLookahead = false;
      lookaheadMultilocks();  // Lookahead with unlocking mechanism.
      // Redo lookahead based on the cores we found before.
      if (redoLookahead) {
        REDO_LOOKAHEAD++;
        assert(activeCores.size() == 0);
        continue;
      } else {
        printAroundSecondLookahead(false);
        break;
      }
    } else {
      printAroundSecondLookahead(false);
      break;
    }
  }
  // Post-condition: all the detected cores should be in localCores.
}

bool Solver::lookaheadQscore() {
  static int64_t thres = 2;

  /* The conflicts number of last lookahead. */
  static uint64_t prevConflicts = 0;

  /* The UB value of last lookahead. */
  static int64_t prevUB = 0;

  static double coef = 1;
  static int myLH = 0;    // number of total lookaheads.
  static int mySucc = 0;  // number of successful lookaheads.

  assert(UB > countedWeight);
  LHconfl = CRef_Undef;
#ifdef FLAG_NO_LA
  return false;
#endif
  int64_t lb = UB - countedWeight;  // The lower bound of satisfied weight.
  if (lb > totalCost - satisfiedWeight - countedWeight) {
    return false;  // Impossible to reach UB.
  }

  if (UB != prevUB) {
    if (UB > prevUB) {
      for (int i = 0; i < Qscores.size(); i++) {
        Qscores[i].no /= 2;
      }
    }
    prevUB = UB;
  }

#ifndef FLAG_ALWAYS_LA
  bool toDo;
  int nbFalsifiedSoftlit = falseLits.size();
  Qscore &qscore = Qscores[nbFalsifiedSoftlit];

  if (conflicts > prevConflicts) {
    // Conflicts number increased, means new conflicts encountered in search
    // progress.
    if (drand(random_seed) < stepSizeLB / 2) {
      toDo = true;
    } else {
      if (myLH > 20) {
        int rate = (mySucc * 100) / myLH;
        if (rate > 75) {
          coef += 0.1;
        } else if (rate < 60 && coef > 0.5) {
          coef -= 0.1;
        }
      }
      toDo = (drand(random_seed) < (1 - (qscore.no - coef * qscore.yes)));

      if (!toDo) {
        skipLAbyprba++;
      }
    }
    prevConflicts = conflicts;
  } else if (lb <= thres) {
    // Smaller lb means easier to find a soft conflict by lookahead.
    toDo = true;
  } else {
    toDo = false;
  }

  if (LOOKAHEAD == nbLKsuccess) {
    // Always success at the beginning, better to do more lookahead.
    toDo = true;
  }
  if (!toDo) {
    skipLA++;
    return true;
  }

  if (stepSizeLB > 0.04) {
    stepSizeLB -= 0.00001;
  }
  myLH += 1;
#endif

  LOOKAHEAD++;
  assert(lookaheadConflictCost == 0);
  assert(activeCores.size() == 0);
  lastConflLits.clear();
#ifndef NDEBUG
  assert(lastCores.size() + freeCores.size() == localCores.size());
#endif
  todoLookahead();

#ifndef FLAG_ALWAYS_LA
  if (softConflictFlag) {
    // Find a soft conflict, lookahead is successful.
    qscore.yes += stepSizeLB * (1 - qscore.yes);
    qscore.no *= (1 - stepSizeLB);
    mySucc += 1;
    totalPrunedLB += lb;
    totalPrunedLB2 += lb * lb;
  } else {
    // Lookahead is not successful.
    qscore.no += stepSizeLB * (1 - qscore.no);
    qscore.yes *= (1 - stepSizeLB);
  }

  // Update the threshold base on the historal success rate.
  int rate = (mySucc * 100) / myLH;
  if (rate > 75) {
    thres = lb;
  } else if (rate > 50) {
    thres = lb - 1;
  } else {
    thres = (lb + lookaheadConflictCost) / 2;
  }
  prevConflicts = conflicts;
#endif
  return activeCores.size() > 0 || LHconfl != CRef_Undef;
}

int64_t Solver::getFalseCoreInitialWeight(int core_id) {
  LocalCore &core = localCores[core_id];
  int64_t falsified_weight = 0;
  for (int j = 0; j < core.coreLits.size(); j++) {
    Lit p = core.coreLits[j].lit;
    if (value(p) == l_False && weights[var(p)] == 0) {
      falsified_weight += core.coreLits[j].weight;
    }
  }
  assert(falsified_weight >= core.weight);
  assert(falsified_weight <= core.falsifiedWeight);
  int64_t initialWeight = falsified_weight - core.weight;
  return initialWeight;
}

void Solver::printCore(int core_id) {
  LocalCore &core = localCores[core_id];
  printf("  core id %d, weight %" PRId64 ", level %d: ", core_id, core.weight,
         core.level);
  for (int j = 0; j < core.coreLits.size(); j++) {
    printf("%d(%" PRId64 "),", toInt(core.coreLits[j].lit),
           core.coreLits[j].weight);
  }
  printf("\n");
}

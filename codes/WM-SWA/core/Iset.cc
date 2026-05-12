#include "../mtl/Sort.h"
#include "Solver.h"

struct LitOrderPartition {
  const vec<int64_t> &weights;
  vec2<Lit, vec<Lit>> &conflictLits;
  bool operator()(Lit x, Lit y) const {
    return conflictLits[x].size() < conflictLits[y].size() ||
           conflictLits[x].size() == conflictLits[y].size() &&
               weights[var(x)] > weights[var(y)];
  }
  LitOrderPartition(const vec<int64_t> &w, vec2<Lit, vec<Lit>> &c)
      : weights(w), conflictLits(c) {}
};

struct IsetOrderWeightInc {
  vec<Iset> &isets;
  bool operator()(int i, int j) const {
    return isets[i].weight < isets[j].weight;
  }
  IsetOrderWeightInc(vec<Iset> &i) : isets(i) {}
};

struct IsetOrderSizeInc {
  vec<Iset> &isets;
  bool operator()(int i, int j) {
    return isets[i].lits.size() < isets[j].lits.size();
  }
  IsetOrderSizeInc(vec<Iset> &i) : isets(i) {}
};

void Solver::printSatisfiedLits(Lit p, int trailRecord) {
  bool someSatisfied = false;
  for (int i = trailRecord + 1; i < trail.size(); i++)
    if (value(trail[i]) == l_True && isSoftLits(trail[i])) someSatisfied = true;

  if (!someSatisfied) return;

  ISET_PRINT(1, "c assume soft literal %d, satisfied: ", toInt(p));
  for (int i = trailRecord + 1; i < trail.size(); i++)
    if (value(trail[i]) == l_True && isSoftLits(trail[i]))
      ISET_PRINT(1, " %d(w=%" PRId64 ")", toInt(trail[i]),
                 weights[var(trail[i])]);
  ISET_PRINT(1, "\n");
}

void Solver::partition2() {
  vec<Lit> remainingLits, candidateLits, iset;
  int i, j;
  int nbIsets = 0;

  int initSoftLits = allSoftLits.size();
  for (int ii = 0; ii < allSoftLits.size(); ii++) {
    Var vv = var(allSoftLits[ii]);
    remainingLits.clear();
    if (!seen[vv]) {
      assert(isSoftLits(vv));
      seen[vv] = 1;
      if (value(vv) == l_Undef && conflictLits[softLits[vv]].size() > 0) {
        remainingLits.push(softLits[vv]);
      } else
        continue;
    } else
      continue;

    // Fill remainingLits with the connected component of remainingLits[0]
    assert(remainingLits.size() == 1);
    for (i = 0; i < remainingLits.size(); i++) {
      Lit p = remainingLits[i];
      const vec<Lit> &lits = conflictLits[p];
      for (j = 0; j < lits.size(); j++) {
        Lit q = lits[j];
        if (!seen[var(q)]) {
          seen[var(q)] = 1;
          if (value(q) == l_Undef) {
            assert(conflictLits[q].size() > 0);
            remainingLits.push(q);
          }
        }
      }
    }

    // prioritize the literals with the smallest number of conflictLits, and
    // then with the largest weight
    sort(remainingLits, LitOrderPartition(weights, conflictLits));

    ISET_PRINT(1, "c partition2, connected component size %d : ",
               remainingLits.size());
    for (i = 0; i < remainingLits.size(); i++)
      ISET_PRINT(1, " %d(w=%" PRId64 ",confl=%d)", toInt(remainingLits[i]),
                 weights[var(remainingLits[i])],
                 conflictLits[remainingLits[i]].size());
    ISET_PRINT(1, "\n");

    // Find the partition of remainingLits
    for (int jj = 0; jj < remainingLits.size(); jj++) {
      Lit pjj = remainingLits[jj];
      if (!isSoftLits(pjj)) continue;

      candidateLits.clear();
      candidateLits.push(pjj);
      vec<Lit> visited;

      // Find the next iset
      iset.clear();
      int64_t minW = INT64_MAX;
      while (candidateLits.size() > 0) {
        // Find the best iset among the candidates
        // Best is the one with the smallest number of conflictLits, and then
        // with the largest weight
        Lit best = candidateLits[0];
        // int idx = 0;
        for (i = 1; i < candidateLits.size(); i++) {
          Lit p = candidateLits[i];
          if (conflictLits[p].size() < conflictLits[best].size() ||
              conflictLits[p].size() == conflictLits[best].size() &&
                  weights[var(p)] > weights[var(best)]) {
            best = p;
            // idx = j;
          }
        }
        if (best != lit_Undef) {
          // Put the candidate into the iset
          iset.push(best);
          if (weights[var(best)] < minW) minW = weights[var(best)];

          const vec<Lit> &lits = conflictLits[best];
          assert(lits.size() > 0);
          candidateLits.clear();
          for (j = 0; j < lits.size(); j++) {
            Lit q = lits[j];
            assert(q != best);
            softVarLocked[var(q)]++;
            if (softVarLocked[var(q)] == 1) visited.push(q);
            if (value(q) == l_Undef && weights[var(q)] > 0 &&
                softVarLocked[var(q)] == iset.size()) {
              candidateLits.push(q);
            }
          }
        }
      }
      for (i = 0; i < visited.size(); i++) softVarLocked[var(visited[i])] = 0;
      if (iset.size() > 1) {
        assert(minW > 0);
        // Construct the iset
        sort(iset, LitOrderWeightDec(weights));

        ISET_PRINT(1, "c iset %d, minW=%" PRId64 " : ", iset.size(), minW);
        for (i = 0; i < iset.size(); i++)
          ISET_PRINT(1, " %d(w=%" PRId64 ")", toInt(iset[i]),
                     weights[var(iset[i])]);
        ISET_PRINT(1, "\n");

        vec<Lit> cl(2, lit_Undef);
        while (iset.size() > 1) {
          assert(minW > 0);
          cl[1] = ~createHardClausesFromLits(iset, minW);
          if (cl[0] != lit_Undef) {
            CRef cr = ca.alloc(cl, false);
            clauses.push(cr);
            attachClause(cr);
          }
          cl[0] = ~cl[1];
          int last = iset.size();
          for (int k = iset.size() - 1; k >= 0; --k) {
            weights[var(iset[k])] -= minW;
            assert(weights[var(iset[k])] >= 0);
            if (weights[var(iset[k])] == 0) {
              removeSoftLit(iset[k]);
              last = k;
            }
          }
          derivedCost += minW * (iset.size() - 1);
          nbIsets++;
          iset.shrink(iset.size() - last);
          if (iset.size() > 0) minW = weights[var(iset.last())];
        }
        jj--;
      }
    }
  }
  for (int ii = 0; ii < allSoftLits.size(); ii++) {
    Var vv = var(allSoftLits[ii]);
    seen[vv] = 0;
  }

  allSoftLits.clear();
  for (i = 0, j = 0; i < unitSoftLits.size(); i++)
    if (softLits[var(unitSoftLits[i])] != lit_Undef) {
      unitSoftLits[j++] = unitSoftLits[i];
      allSoftLits.push(unitSoftLits[i]);
    }
  unitSoftLits.shrink(i - j);
  for (i = 0, j = 0; i < nonUnitSoftLits.size(); i++)
    if (softLits[var(nonUnitSoftLits[i])] != lit_Undef) {
      nonUnitSoftLits[j++] = nonUnitSoftLits[i];
      allSoftLits.push(nonUnitSoftLits[i]);
    }
  nonUnitSoftLits.shrink(i - j);
  assert(allSoftLits.size() == nSoftLits);
  weights.copyTo(weightsBckp);
  printf("c isets %d, derivedCost %" PRId64
         ", reduction of soft from %d to %d\n",
         nbIsets, derivedCost, initSoftLits, nSoftLits);
}

bool Solver::getSoftLitIncompatibilities() {
#ifdef printIncompatibilities
  int initTrail = trail.size(), nbConflLits = 0, nbFailedLits = 0,
      nbConfLits2 = 0;
#endif
  CRef confl;
  int i, j;

  // Could be improved, no need to have a list for both literals,
  // just one list per var
  falseLits.clear();
  setTrailRecord();
  for (i = 0; i < unitSoftLits.size(); i++) {
    conflictLits[unitSoftLits[i]].clear();
  }
  for (i = 0; i < unitSoftLits.size(); i++) {
    Lit p = unitSoftLits[i];
    if (value(p) != l_Undef) continue;
    simpleUncheckEnqueue(p);
    confl = simplePropagate();
    if (confl != CRef_Undef || softConflictFlag) {
      cancelUntilTrailRecord();
      softConflictFlag = false;
      uncheckedEnqueue(~p);
      if (propagate() != CRef_Undef || softConflictFlag) {
        // both value true and false cause a conflict, unsat
        return false;
      }
      setTrailRecord();
#ifdef printIncompatibilities
      nbFailedLits++;
#endif
    } else {
      if (falseLits.size() > 0) {
#ifdef printIncompatibilities
        nbConflLits += falseLits.size();
#endif
        for (j = falseLitsRecord; j < falseLits.size(); j++)
          addConflictLit(p, falseLits[j]);
      }
      printSatisfiedLits(p, trailRecord);
      cancelUntilTrailRecord();
    }
  }
#ifdef printIncompatibilities
  printf(
      "c conflLits %d, conflLits2 %d, nbFailedLits %d, fixedVarsBypreproc %d, "
      "totalFixedVars %d\n",
      nbConflLits, nbConfLits2, nbFailedLits, trail.size() - initTrail,
      trail.size());
#endif
  return true;
}

bool Solver::getSoftLitIncompatibilities2() {
#ifdef printIncompatibilities
  int initTrail = trail.size(), nbConflLits = 0, nbFailedLits = 0,
      nbConfLits2 = 0;
#endif
  CRef confl;
  int i, j;

  // Could be improved, no need to have a list for both literals,
  // just one list per var
  falseLits.clear();
  setTrailRecord();
  for (i = 0; i < allSoftLits.size(); i++) {
    conflictLits[allSoftLits[i]].clear();
  }
  for (i = 0; i < allSoftLits.size(); i++) {
    Lit p = allSoftLits[i];
    if (value(p) != l_Undef) continue;
    simpleUncheckEnqueue(p);
    confl = simplePropagate();
    if (confl != CRef_Undef || softConflictFlag) {
      cancelUntilTrailRecord();
      softConflictFlag = false;
      uncheckedEnqueue(~p);
      if (propagate() != CRef_Undef || softConflictFlag == true) {
        return false;
      }
      setTrailRecord();
      // trailRecord = trail.size();   falseLitsRecord = falseLits.size();
#ifdef printIncompatibilities
      nbFailedLits++;
#endif
    } else {
      if (falseLits.size() > 0) {
#ifdef printIncompatibilities
        nbConflLits += falseLits.size() - falseLitsRecord;
#endif
        for (j = 0; j < falseLits.size(); j++) addConflictLit(p, falseLits[j]);
      }
      cancelUntilTrailRecord();
    }
  }
  softLitsWithNonNeighbors.clear();
  softLitsWithoutNonNeighbors.clear();
  for (i = 0; i < allSoftLits.size(); i++) {
    if (conflictLits[allSoftLits[i]].size() > 0)
      softLitsWithNonNeighbors.push(allSoftLits[i]);
    else
      softLitsWithoutNonNeighbors.push(allSoftLits[i]);
  }
#ifdef printIncompatibilities
  printf(
      "c conflLits %d, conflLits2 %d, nbFailedLits %d, fixedVarsBypreproc %d, "
      "totalFixedVars %d\n",
      nbConflLits, nbConfLits2, nbFailedLits, trail.size() - initTrail,
      trail.size());
#endif
  return true;
}

void Solver::getIsets(vec<Iset> &isets, vec<int> &isetids) {
  isets.clear();
  vec<Lit> remainingLits, candidateLits, isetLits;
  int i, j;
  int nbIsets = 0;

  int initSoftLits = allSoftLits.size();
  for (int ii = 0; ii < allSoftLits.size(); ii++) {
    Var vv = var(allSoftLits[ii]);
    remainingLits.clear();
    if (!seen[vv]) {
      assert(isSoftLits(vv));
      seen[vv] = 1;
      if (value(vv) == l_Undef && conflictLits[softLits[vv]].size() > 0) {
        remainingLits.push(softLits[vv]);
      } else
        continue;
    } else
      continue;

    // Fill remainingLits with the connected component of remainingLits[0]
    assert(remainingLits.size() == 1);
    for (i = 0; i < remainingLits.size(); i++) {
      Lit p = remainingLits[i];
      const vec<Lit> &lits = conflictLits[p];
      for (j = 0; j < lits.size(); j++) {
        Lit q = lits[j];
        if (!seen[var(q)]) {
          seen[var(q)] = 1;
          if (value(q) == l_Undef) {
            assert(conflictLits[q].size() > 0);
            remainingLits.push(q);
          }
        }
      }
    }

    // prioritize the literals with the smallest number of conflictLits, and
    // then with the largest weight
    sort(remainingLits, LitOrderPartition(weights, conflictLits));

    ISET_PRINT(
        1, "c getIsets, connected component size %d : ", remainingLits.size());
    for (i = 0; i < remainingLits.size(); i++)
      ISET_PRINT(1, " %d(w=%" PRId64 ",confl=%d)", toInt(remainingLits[i]),
                 weights[var(remainingLits[i])],
                 conflictLits[remainingLits[i]].size());
    ISET_PRINT(1, "\n");

    // Find the partition of remainingLits
    for (int jj = 0; jj < remainingLits.size(); jj++) {
      Lit pjj = remainingLits[jj];
      if (seen[var(pjj)] == 2 || !isSoftLits(pjj)) continue;

      candidateLits.clear();
      candidateLits.push(pjj);
      vec<Lit> visited;

      // Find the next iset
      isetLits.clear();
      int64_t minW = INT64_MAX;
      while (candidateLits.size() > 0) {
        // Find the best soft lits among the candidates
        // Best is the one with the smallest number of conflictLits, and then
        // with the largest weight
        Lit best = candidateLits[0];
        for (i = 1; i < candidateLits.size(); i++) {
          Lit p = candidateLits[i];
          if (conflictLits[p].size() < conflictLits[best].size() ||
              conflictLits[p].size() == conflictLits[best].size() &&
                  weights[var(p)] > weights[var(best)]) {
            best = p;
            // idx = j;
          }
        }

        if (best != lit_Undef) {
          // Put the best candidate into the iset
          isetLits.push(best);
          if (weights[var(best)] < minW) minW = weights[var(best)];

          const vec<Lit> &lits = conflictLits[best];
          assert(lits.size() > 0);
          candidateLits.clear();
          for (j = 0; j < lits.size(); j++) {
            Lit q = lits[j];
            assert(q != best);
            softVarLocked[var(q)]++;
            if (softVarLocked[var(q)] == 1) visited.push(q);
            if (value(q) == l_Undef && seen[var(q)] != 2 &&
                softVarLocked[var(q)] == isetLits.size()) {
              candidateLits.push(q);
            }
          }
        }
      }
      for (i = 0; i < visited.size(); i++) softVarLocked[var(visited[i])] = 0;

      // record the new iset
      if (isetLits.size() > 1) {
        assert(minW > 0);
        sort(isetLits, LitOrderWeightDec(weights));
        int isetid = isets.size();
        isets.push();
        isetids.push(isetid);
        isets[isetid].weight = minW;
        for (int k = 0; k < isetLits.size(); k++) {
          Lit p = isetLits[k];
          seen[var(p)] = 2;
          isets[isetid].lits.push(p);
          if (k != 0) derivedCost += weights[var(p)];
        }
        nbIsets++;
        ISET_PRINT(1, "c iset id %d, size %d, minW=%" PRId64 " : ", isetid,
                   isetLits.size(), minW);
        for (i = 0; i < isets[isetid].lits.size(); i++)
          ISET_PRINT(1, " %d(w=%" PRId64 ")", toInt(isets[isetid].lits[i]),
                     weights[var(isets[isetid].lits[i])]);
        ISET_PRINT(1, "\n");
      }
    }
  }
  for (int ii = 0; ii < allSoftLits.size(); ii++) {
    Var vv = var(allSoftLits[ii]);
    seen[vv] = 0;
  }

  /*allSoftLits.clear();
  for (i = 0, j = 0; i < unitSoftLits.size(); i++)
      if (softLits[var(unitSoftLits[i])] != lit_Undef)
      {
          unitSoftLits[j++] = unitSoftLits[i];
          allSoftLits.push(unitSoftLits[i]);
      }
  unitSoftLits.shrink(i - j);
  for (i = 0, j = 0; i < nonUnitSoftLits.size(); i++)
      if (softLits[var(nonUnitSoftLits[i])] != lit_Undef)
      {
          nonUnitSoftLits[j++] = nonUnitSoftLits[i];
          allSoftLits.push(nonUnitSoftLits[i]);
      }
  nonUnitSoftLits.shrink(i - j);
  assert(allSoftLits.size() == nSoftLits);
  weights.copyTo(weightsBckp);*/
  printf("c isets %d, derivedCost %" PRId64
         ", reduction of soft from %d to %d\n",
         nbIsets, derivedCost, initSoftLits, nSoftLits);
}

// we can use the conflicted and picked arrays because we only modifies these
// arrays for free lits
bool Solver::getIsets2(vec<Iset> &isets, vec<int> &isetids) {
  isets.clear();
  vec<Lit> workingSet;
  int initEnd0;
#ifdef printIncompatibilities
  int totalSize = 0;
#endif

  for (int i = 0; i < softLitsWithNonNeighbors.size(); i++) {
    Lit p = softLitsWithNonNeighbors[i];
    if (value(p) == l_Undef && conflictLits[p].size() > 0) {
      conflicted[var(p)] = 0;
      picked[var(p)] = 0;
      workingSet.push(p);
    }
  }

  initEnd0 = workingSet.size();
  while (workingSet.size() > 0) {
    int begin = 0, end = workingSet.size(), isetSize = 0,
        initEnd = workingSet.size();
    int isetid = isets.size();
    isets.push();
    isetids.push(isetid);
    isetSize = 0;
    vec<Lit> &isetLits = isets[isetid].lits;
    int64_t minW = INT64_MAX;
    while (begin < end) {
      int min = allSoftLits.size();
      Lit minLit = lit_Undef;
      for (int i = begin; i < end;
           i++) {  // choose the soft lit with least nonneibors
        Lit p = workingSet[i];
        assert(picked[var(p)] == 0 && value(p) == l_Undef);
        int nbNonNeibors = 0;
        vec<Lit> &nonNeibors = conflictLits[p];
        for (int j = 0; j < nonNeibors.size(); j++) {
          Lit q = nonNeibors[j];
          if (picked[var(q)] == 0 && value(q) == l_Undef) nbNonNeibors++;
        }
        if (nbNonNeibors < min) {
          minLit = p;
          min = nbNonNeibors;  // conflictLits[minLit].size();
        }
      }
      assert(minLit != lit_Undef);
      isetLits.push(minLit);
      if (minW > weights[var(minLit)]) minW = weights[var(minLit)];
      picked[var(minLit)] = true;
      vec<Lit> &nonNeibors = conflictLits[minLit];
      for (int i = 0; i < nonNeibors.size(); i++) {
        Lit p = nonNeibors[i];
        if (picked[var(p)] == 0 && conflicted[var(p)] == (uint32_t)isetSize &&
            value(p) == l_Undef) {
          conflicted[var(p)]++;
          workingSet.push(p);
        }
      }
      begin = end;
      end = workingSet.size();
      isetSize++;
    }
#ifdef printIncompatibilities
    totalSize += isetLits.size();
#endif
    isets[isetid].weight = minW;
    int i, j;
    for (i = 0, j = 0; i < initEnd; i++) {
      Lit p = workingSet[i];
      if (picked[var(p)] == 0) workingSet[j++] = p;
      conflicted[var(p)] = 0;
    }  // remove picked lits from workingSet
    workingSet.shrink(workingSet.size() - j);
  }
#ifdef printIncompatibilities
  printf(
      "c %d isets by partition with total size %d among the %d soft lits with "
      "nonNeibors\n",
      isets.size(), totalSize, initEnd0);

#endif
  return true;
}

bool Solver::pass2end(vec<Iset> &isets, vec<int> &isetids) {
  vec<Lit> workingSet;
  for (int i = isetids.size() - 1; i >= 0; i--) {
    int targetid = isetids[i];
    vec<Lit> &targetLits = isets[targetid].lits;
    if (targetLits.size() == 0) continue;
    // find commun nonNeibors of iset
    for (int j = 0; j < targetLits.size(); j++) {
      vec<Lit> &nonNeibors = conflictLits[targetLits[j]];
      if (nonNeibors.size() < targetLits.size()) {
        assert(nonNeibors.size() == targetLits.size() - 1);
        continue;
      }
      for (int b = 0; b < nonNeibors.size(); b++) {
        Lit p = nonNeibors[b];
        if (value(p) == l_Undef) {
          if (conflicted[var(p)] == 0) workingSet.push(p);
          conflicted[var(p)]++;
        }
      }
    }

    for (int k = 0; k < i; k++) {
      int sourceid = isetids[k];
      vec<Lit> &sourceLits = isets[sourceid].lits;
      if (sourceLits.size() == 0) continue;
      for (int a = 0; a < sourceLits.size();) {
        Lit p = sourceLits[a];
        if (conflicted[var(p)] == (uint32_t)targetLits.size()) {
          targetLits.push(p);  // the iset size is increased by 1
          sourceLits[a] = sourceLits.last();
          sourceLits.shrink(1);  // p is removed from source lits
          ISET_PRINT(1,
                     "c pass2end: move lit %d(w=%" PRId64
                     ") from iset %d to iset %d\n",
                     toInt(p), weights[var(p)], sourceid, targetid);
          vec<Lit> &nonNeibors = conflictLits[p];
          for (int b = 0; b < nonNeibors.size(); b++) {
            Lit q = nonNeibors[b];
            if (value(q) == l_Undef) {
              if (conflicted[var(q)] == 0) workingSet.push(q);
              conflicted[var(q)]++;
            }
          }
        } else
          a++;
      }
      if (sourceLits.size() == 0) {
#ifdef printIncompatibilities
        printf("c iset %d becomes empty in pass to end\n", sourceid);
#endif
      }
    }
    for (int b = 0; b < workingSet.size(); b++)
      conflicted[var(workingSet[b])] = 0;
    workingSet.clear();
  }
  return true;
}

bool Solver::pass2begin(vec<Iset> &isets, vec<int> &isetids) {
  vec<Lit> workingSet;
  for (int i = 0; i < isetids.size(); i++) {
    int targetid = isetids[i];
    vec<Lit> &targetLits = isets[targetid].lits;
    if (targetLits.size() == 0) continue;
    // find commun nonNeibors of iset
    for (int j = 0; j < targetLits.size(); j++) {
      vec<Lit> &nonNeibors = conflictLits[targetLits[j]];
      if (nonNeibors.size() < targetLits.size()) {
        assert(nonNeibors.size() == targetLits.size() - 1);
        continue;
      }
      for (int b = 0; b < nonNeibors.size(); b++) {
        Lit p = nonNeibors[b];
        if (value(p) == l_Undef) {
          if (conflicted[var(p)] == 0) workingSet.push(p);
          conflicted[var(p)]++;
        }
      }
    }

    for (int k = i + 1; k < isetids.size(); k++) {
      int sourceid = isetids[k];
      vec<Lit> &sourceLits = isets[sourceid].lits;
      if (sourceLits.size() == 0) continue;
      for (int a = 0; a < sourceLits.size();) {
        Lit p = sourceLits[a];
        if (conflicted[var(p)] == (uint32_t)targetLits.size()) {
          targetLits.push(p);  // the iset size is increased by 1
          sourceLits[a] = sourceLits.last();
          sourceLits.shrink(1);  // p is removed from source lits
          ISET_PRINT(1,
                     "c pass2begin: move lit %d(w=%" PRId64
                     ") from iset %d to iset %d\n",
                     toInt(p), weights[var(p)], sourceid, targetid);
          vec<Lit> &nonNeibors = conflictLits[p];
          for (int b = 0; b < nonNeibors.size(); b++) {
            Lit q = nonNeibors[b];
            if (value(q) == l_Undef) {
              if (conflicted[var(q)] == 0) workingSet.push(q);
              conflicted[var(q)]++;
            }
          }
        } else
          a++;
      }
      if (sourceLits.size() == 0) {
#ifdef printIncompatibilities
        printf("c iset %d becomes empty in pass to begin\n", sourceid);
#endif
      }
    }
    for (int b = 0; b < workingSet.size(); b++)
      conflicted[var(workingSet[b])] = 0;
    workingSet.clear();
  }
  return true;
}

bool Solver::pass2large(vec<Iset> &isets, vec<int> &isetids) {
  sort(isetids, IsetOrderSizeInc(isets));
#ifdef printIncompatibilities
  for (int i = isetids.size() - 1; i >= 0; i--)
    assert(i == isetids.size() - 1 ||
           isets[isetids[i]].lits.size() <= isets[isetids[i + 1]].lits.size());
#endif

  vec<Lit> workingSet;
  for (int i = isetids.size() - 1; i >= 0; i--) {
    int targetid = isetids[i];
    vec<Lit> &targetLits = isets[targetid].lits;
    if (targetLits.size() == 0) continue;
    // find commun nonNeibors of iset
    for (int j = 0; j < targetLits.size(); j++) {
      vec<Lit> &nonNeibors = conflictLits[targetLits[j]];
      if (nonNeibors.size() < targetLits.size()) {
        assert(nonNeibors.size() == targetLits.size() - 1);
        continue;
      }
      for (int b = 0; b < nonNeibors.size(); b++) {
        Lit p = nonNeibors[b];
        if (value(p) == l_Undef) {
          if (conflicted[var(p)] == 0) workingSet.push(p);
          conflicted[var(p)]++;
        }
      }
    }

    for (int k = 0; k < i; k++) {
      int sourceid = isetids[k];
      vec<Lit> &sourceLits = isets[sourceid].lits;
      if (sourceLits.size() == 0) continue;
      for (int a = 0; a < sourceLits.size();) {
        Lit p = sourceLits[a];
        if (conflicted[var(p)] == (uint32_t)targetLits.size()) {
          targetLits.push(p);  // the iset size is increased by 1
          sourceLits[a] = sourceLits.last();
          sourceLits.shrink(1);  // p is removed from lits
          ISET_PRINT(1,
                     "c pass2large: move lit %d(w=%" PRId64
                     ") from iset %d to iset %d\n",
                     toInt(p), weights[var(p)], sourceid, targetid);
          vec<Lit> &nonNeibors = conflictLits[p];
          for (int b = 0; b < nonNeibors.size(); b++) {
            Lit q = nonNeibors[b];
            if (value(q) == l_Undef) {
              if (conflicted[var(q)] == 0) workingSet.push(q);
              conflicted[var(q)]++;
            }
          }
        } else
          a++;
      }
      if (sourceLits.size() == 0) {
#ifdef printIncompatibilities
        printf("c iset %d becomes empty in pass to large\n", sourceid);
#endif
      }
    }
    for (int b = 0; b < workingSet.size(); b++)
      conflicted[var(workingSet[b])] = 0;
    workingSet.clear();
  }
  return true;
}

void Solver::mapIsets(vec<Iset> &isets, vec<int> &isetids) {
  derivedCost = 0;
  int nbIsets = 0;
  int initSoftLits = allSoftLits.size();

  for (int i = 0; i < isetids.size(); i++) {
    int isetid = isetids[i];
    vec<Lit> &lits = isets[isetid].lits;
    if (lits.size() == 0) continue;
    sort(lits, LitOrderWeightDec(weights));
    int64_t minW = weights[var(lits.last())];
    assert(minW > 0);

    vec<Lit> cl(2, lit_Undef);
    while (lits.size() > 1) {
      cl[1] = ~createHardClausesFromLits(lits, minW);
      if (cl[0] != lit_Undef) {
        CRef cr = ca.alloc(cl, false);
        clauses.push(cr);
        attachClause(cr);
      }
      cl[0] = ~cl[1];
      int last = lits.size();
      for (int k = lits.size() - 1; k >= 0; --k) {
        weights[var(lits[k])] -= minW;
        assert(weights[var(lits[k])] >= 0);
        if (weights[var(lits[k])] == 0) {
          removeSoftLit(lits[k]);
          last = k;
        }
      }
      derivedCost += minW * (lits.size() - 1);
      nbIsets++;
      lits.shrink(lits.size() - last);
      if (lits.size() > 0) minW = weights[var(lits.last())];
    }
  }

  allSoftLits.clear();
  int i, j;
  for (i = 0, j = 0; i < unitSoftLits.size(); i++)
    if (softLits[var(unitSoftLits[i])] != lit_Undef) {
      unitSoftLits[j++] = unitSoftLits[i];
      allSoftLits.push(unitSoftLits[i]);
    }
  unitSoftLits.shrink(i - j);
  for (i = 0, j = 0; i < nonUnitSoftLits.size(); i++)
    if (softLits[var(nonUnitSoftLits[i])] != lit_Undef) {
      nonUnitSoftLits[j++] = nonUnitSoftLits[i];
      allSoftLits.push(nonUnitSoftLits[i]);
    }
  nonUnitSoftLits.shrink(i - j);
  assert(allSoftLits.size() == nSoftLits);
  weights.copyTo(weightsBckp);
  printf("c isets %d, derivedCost %" PRId64
         ", reduction of soft from %d to %d\n",
         nbIsets, derivedCost, initSoftLits, nSoftLits);
  weights.copyTo(weightsBckp);
}

bool Solver::findIndependentSets() {
  if (!getSoftLitIncompatibilities2()) return false;

  vec<Iset> isets;
  vec<int> isetids;

  getIsets2(isets, isetids);

  ISET_PRINT(1, "c find %d isets :\n", isets.size());
  for (int i = 0; i < isetids.size(); i++) {
    int id = isetids[i];
    vec<Lit> &lits = isets[id].lits;
    ISET_PRINT(1, "c iset id %d, size %d, weight %" PRId64 " : ", id,
               lits.size(), isets[id].weight);
    for (int j = 0; j < lits.size(); j++)
      ISET_PRINT(1, " %d(w=%" PRId64 ")", toInt(lits[j]),
                 weights[var(lits[j])]);
    ISET_PRINT(1, "\n");
  }

  pass2end(isets, isetids);
  pass2begin(isets, isetids);
  pass2large(isets, isetids);
  mapIsets(isets, isetids);

  return true;
}
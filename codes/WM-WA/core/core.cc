#include "../mtl/Sort.h"
#include "PrintFlags.h"
#include "Solver.h"

void Solver::collectCoreLitsTobeAssigned(int coreid) {
  LocalCore &core = localCores[coreid];
  assert(core.coreLits.size() != 0);
  for (int i = 0; i < core.coreLits.size(); i++) {
    Lit p = core.coreLits[i].lit;
    if (value(p) != l_Undef) continue;
    litsTobeAssigned.push(~p);
    coresTobeAssigned.push(coreid);
  }
}

void Solver::analyzeInAssignCoreLits(vec<Lit> &out_learnt, int coreid) {
  int pathC = 0;
  out_learnt.clear();
  int index = trail.size() - 1;
  assert(countedWeight + lookaheadConflictCost < UB);
  int maxConflLevel = 0;

  vec<Lit> ori_learnt;
  ori_learnt.clear();
  LocalCore &core = localCores[coreid];
  for (int i = 0; i < core.coreLits.size(); i++) {
    Lit q = core.coreLits[i].lit;
    Var v = var(q);
    if (seen2[var(q)] == counter || value(q) == l_False) continue;
    assert(value(q) == l_True && level(var(q)) == decisionLevel());
    ori_learnt.push(~q);
    if (level(v) > maxConflLevel) maxConflLevel = level(v);
  }

  for (int i = 0; i < core.reasons.size(); i++) {
    Lit q = core.reasons[i];
    Var v = var(q);
    assert(value(q) == l_False && seen2[v] != counter);
    assert(level(v) <= maxConflLevel);
    if (level(v) > 0) ori_learnt.push(q);
  }
  assert(ori_learnt.size() > 0);

  if (maxConflLevel == 0) return;

  out_learnt.push();
  out_learnt.push();
  for (int i = 0; i < ori_learnt.size(); i++) {
    Lit q = ori_learnt[i];
    Var v = var(q);
    if (!seen[v] && !redundantLit(q)) {
      seen[v] = 1;
      if (level(v) >= maxConflLevel)
        pathC++;
      else
        out_learnt.push(q);
    }
  }

  assert(pathC > 0 && maxConflLevel == decisionLevel());
  CRef confl;
  vec<Lit> c2;
  Lit p = lit_Undef;

  while (pathC > 0) {
    while (!seen[var(trail[index--])]);
    p = trail[index + 1];
    confl = reason(var(p));
    seen[var(p)] = 0;
    pathC--;

    if (pathC == 0) break;

    bool hardenedLit = isSoftLits(p) && hardened[var(p)];
    bool fromHarden = false;
    if (hardenedLit) {
      Clause &c = ca[confl];
      c[0] = p;
      int lbd = computeLBD(c);
      // Virtual clause, need to be created
      if (lbd <= tier2_lbd_cut) {
        fromHarden = true;
        // Important to make a copy, since alloc may reallocate 'c'
        getClauseLits(c, c2);
        confl = ca.alloc(c2, true);
        attachClause(confl);
      } else {
        for (int j = 1; j < c.size(); j++) {
          Lit q = c[j];
          Var v = var(q);
          if (level(v) > 0) {
            if (!seen[v] && !redundantLit(q)) {
              seen[v] = 1;
              if (level(v) >= maxConflLevel)
                pathC++;
              else
                out_learnt.push(q);
            }
          }
        }
      }
    }
    if (!hardenedLit || fromHarden) {
      assert(confl != CRef_Undef);  // (otherwise should be UIP)
      Clause &c = ca[confl];
      fixBinClauseOrder(c);

      updateClauseUse(confl, fromHarden);
      assert(!fromHarden || c.mark() == CORE || c.mark() == TIER2);

      for (int j = 1; j < c.size(); j++) {
        Lit q = c[j];

        if (!seen[var(q)] && level(var(q)) > 0 && !redundantLit(q)) {
          seen[var(q)] = 1;
          if (level(var(q)) >= maxConflLevel) {
            pathC++;
          } else
            out_learnt.push(q);
        }
      }
    }
  }
  out_learnt[1] = ~p;
  for (int i = 1; i < out_learnt.size(); i++) seen[var(out_learnt[i])] = 0;
}

void Solver::conflictInAssignCoreLits(int i, CRef &confl) {
  vec<Lit> learnt_clause;
  int coreid = coresTobeAssigned[i];
  counter++;
  for (int j = i; j >= 0; j--)
    if (coresTobeAssigned[j] == coreid)
      seen2[var(litsTobeAssigned[j])] = counter;
    else
      break;
  for (int j = i + 1; j < coresTobeAssigned.size(); j++)
    if (coresTobeAssigned[j] == coreid)
      seen2[var(litsTobeAssigned[j])] = counter;
    else
      break;

  analyzeInAssignCoreLits(learnt_clause, coreid);

  if (learnt_clause.size() == 0) {
    cancelUntil(0);
    coreConflictIn0 = true;
    return;
  }
  learnt_clause[0] = litsTobeAssigned[i];

  confl = ca.alloc(learnt_clause, true);
  hardens.push(confl);
  attachClause(confl);

  litsTobeAssigned.clear();
  coresTobeAssigned.clear();
}

bool Solver::assignmentsInAssignCoreLits() {
  assert(countedWeight + lookaheadConflictCost < UB);
  int prevTrailSize = trail.size();
  int prevCoreid = -1;
  int nextI = 0;
  int prevI = 0;
  bool unassigned = false;
  vec<Lit> learnt_clause;
  while (nextI < litsTobeAssigned.size() &&
         countedWeight + lookaheadConflictCost < UB) {
    counter++;
    unassigned = false;
    prevI = nextI;
    int i = nextI;
    prevCoreid = coresTobeAssigned[i];
    for (; i < litsTobeAssigned.size() && coresTobeAssigned[i] == prevCoreid;
         i++) {
      seen2[var(litsTobeAssigned[i])] = counter;
      assert(value(litsTobeAssigned[i]) != l_False);
      if (value(litsTobeAssigned[i]) == l_Undef) unassigned = true;
    }
    nextI = i;

    if (!unassigned) continue;

    assert(prevI < nextI);
    analyzeInAssignCoreLits(learnt_clause, prevCoreid);
    CRef cr = CRef_Undef;
    if (learnt_clause.size() > 0) {
      for (i = prevI; i < nextI; i++) {
        Lit p = litsTobeAssigned[i];
        if (value(p) == l_True) continue;
        learnt_clause[0] = p;
        cr = ca.alloc(learnt_clause, true);
        uncheckedEnqueue(p, cr);
        hardens.push(cr);
        if (countedWeight + lookaheadConflictCost >= UB) break;
      }
    } else {
      for (i = prevI; i < nextI; i++) {
        Lit p = litsTobeAssigned[i];
        if (value(p) == l_True) continue;
        uncheckedEnqueue(p, CRef_Undef);
        if (countedWeight + lookaheadConflictCost >= UB) break;
      }
    }
  }
  litsTobeAssigned.clear();
  coresTobeAssigned.clear();
  if (countedWeight + lookaheadConflictCost >= UB) softConflictFlag = true;
  return softConflictFlag || prevTrailSize < trail.size();
}

bool Solver::assignCoreLits(CRef &confl) {
  if (litsTobeAssigned.size() == 0) return false;
  assert(activeCores.size() > 0 &&
         litsTobeAssigned.size() == coresTobeAssigned.size());

  bool unassigned = false;
  for (int i = 0; i < litsTobeAssigned.size(); i++)
    if (value(litsTobeAssigned[i]) == l_False) {
      conflictInAssignCoreLits(i, confl);
      return true;
    } else if (value(litsTobeAssigned[i]) == l_Undef)
      unassigned = true;
  if (unassigned) return assignmentsInAssignCoreLits();
  return false;
}

void Solver::resetCoresData() {
  setTrailRecord();
  activeCores.clear();
  assignedVars.clear();
  TodoSecondLookahead = false;
#ifndef NDEBUG
  // Debug check: all cores should be empty after cleaning.
  for (int i = 0; i < varsInCores.size(); i++) {
    assert(coresOfVar[varsInCores[i]].size() == 0);
  }
#endif
}

void Solver::updateCoreAfterAssignment(int coreid) {
  LocalCore &core = localCores[coreid];

  // Mark seen flag to avoid recompution the weights for the same core.
  if (core.seen) return;
  core.seen = true;

  core.falsifiedWeight = 0;

  // The sum of weights of unassigned literals in core.
  int64_t unassignedWeight = 0;

  for (int i = 0; i < core.coreLits.size(); i++) {
    Lit p = core.coreLits[i].lit;
    Var v = var(p);
    if (value(p) == l_False) {
      core.falsifiedWeight += core.coreLits[i].weight;
      // TODO: can this be moved outside the loop?
      weights[v] += core.coreLits[i].weight;
      hardenHeap.update(v);
      countedWeight += core.coreLits[i].weight;
      core.coreLits[i].weight = 0;
    } else if (value(p) == l_True) {
      // TODO: can this be moved outside the loop?
      weights[v] += core.coreLits[i].weight;
      hardenHeap.update(v);
      satisfiedWeight += core.coreLits[i].weight;
      // Release the lock for this literal on the core.
      core.coreLits[i].weight = 0;
    } else {
      unassignedWeight += core.coreLits[i].weight;
    }
  }

  if (core.falsifiedWeight > 0) {
    /* Decrease the (locked) weight of the core. When core.falsifiedWeight >
     * core.weight, the core is unlocked. */
    lookaheadConflictCost -=
        core.falsifiedWeight > core.weight ? core.weight : core.falsifiedWeight;
    core.weight -=
        core.falsifiedWeight > core.weight ? core.weight : core.falsifiedWeight;
    core.falsifiedWeight = 0;
  }

  if (unassignedWeight <= core.weight && core.weight > 0) {
    collectCoreLitsTobeAssigned(coreid);
  }
}

void Solver::updateCoresAfterAssignment() {
  for (int i = 0; i < assignedVars.size(); i++) {
    Var v = assignedVars[i];
    for (int j = 0; j < coresOfVar[v].size(); j++) {
      updateCoreAfterAssignment(coresOfVar[v][j]);
    }
    if (weights[v] != weightsBckp[v]) {
      LAM_PRINT(LOOKAHEAD,
                "c v %d, weights[v] %" PRId64 ", weightsBckp[v] %" PRId64 " \n",
                v, weights[v], weightsBckp[v]);
    }
    assert(weights[v] == weightsBckp[v]);
    coresOfVar[v].shrink(coresOfVar[v].size());
  }
  assignedVars.clear();
  for (int i = 0; i < activeCores.size(); i++) {
    localCores[activeCores[i]].seen = false;
  }
}

int Solver::pickCoreIdx() {
  int core;
  if (freeCores.size() == 0) {
    core = localCores.size();
    localCores.push();
  } else {
    core = freeCores.last();
    freeCores.pop();
    LocalCore &c = localCores[core];
    c.reset();
  }
  return core;
}

int64_t Solver::setInitialWeight() {
  if (falseVar != var_Undef) {
    return weights[falseVar];
  } else if (falseCore != core_Undef) {
    return falseCoreInitWeight;
  }
  return INT64_MAX;
}

/* Calculate the core weight, locked weights for each literal for the new core.
 */
void Solver::setLitWeightBeforeCancelAssignment(int coreid) {
  // eg: c1={s1, s2, s3}, c2={s3, s4, s5}; propagate s6 -> falsify s3 -> unlock
  // c1, c2(subCores).
#ifndef NDEBUG
  int64_t prevLaConflictCost = lookaheadConflictCost;
#endif
  // The incremental weight of the new core.
  int64_t minWeight = setInitialWeight();
  LocalCore &core = localCores[coreid];
  int64_t subcoresWeightSum = 0;  // eg: w(c1) + w(c2)

  if (subCores.size() > 0)
    for (int i = 0; i < subCores.size(); i++) {
      lookaheadConflictCost -=
          localCores[subCores[i]].weight;  // eg: delete c1 and c2.
      subcoresWeightSum += localCores[subCores[i]].weight;
    }

  int trailLoc = trail.size();
  assistantWeight currentWeight;
  keyAssignmentWeight.clear();
  for (int i = 0; i < keyAssignment.size(); i++) {
    Lit p = keyAssignment[i];
    Var v = var(p);
    trailLoc = trailIndex(v);
    currentWeight.reset();
    currentWeight.freeWeight = weights[v];

    // eg: for each soft literals in the binary tree like: s6, s1, s4
    // calculate the part of wlock(s1, c1) + wlock(s1, c2) + ...
    for (int j = 0; j < coresOfVar[v].size(); j++)
      if (localCores[coresOfVar[v][j]].seen &&
          localCores[coresOfVar[v][j]].unlockedIndex <= trailLoc) {
        for (int k = 0; k < localCores[coresOfVar[v][j]].coreLits.size(); k++)
          if (localCores[coresOfVar[v][j]].coreLits[k].lit == p) {
            currentWeight.inSubcoreWeight +=
                localCores[coresOfVar[v][j]].coreLits[k].weight;
            break;
          }
        assert(currentWeight.inSubcoreWeight > 0);
      }

    if (currentWeight.sum() < minWeight) minWeight = currentWeight.sum();
    keyAssignmentWeight.push(currentWeight);
  }

  // Calculate the locked weights for each soft literals in the new core.
  for (int i = 0; i < keyAssignment.size(); i++) {
    assert(weightsBckp[var(keyAssignment[i])] >=
           keyAssignmentWeight[i].freeWeight +
               keyAssignmentWeight[i].inSubcoreWeight);
    if (keyAssignmentWeight[i].freeWeight > 0 &&
        minWeight > keyAssignmentWeight[i].inSubcoreWeight) {
      assert(keyAssignmentWeight[i].freeWeight >=
             minWeight - keyAssignmentWeight[i].inSubcoreWeight);
      keyAssignmentWeight[i].freeWeight =
          minWeight - keyAssignmentWeight[i].inSubcoreWeight;
    } else
      keyAssignmentWeight[i].freeWeight = 0;
  }

  // Add the soft literals from binary tree into the new core.
  core.coreLits.clear();
  for (int i = keyAssignment.size() - 1; i >= 0; i--) {
    Lit p = keyAssignment[i];
    Var v = var(p);
    weights[v] -= keyAssignmentWeight[i].freeWeight;
    hardenHeap.update(v);
    assert(!seen[var(p)]);
    core.coreLits.push(
        coreLit(keyAssignment[i], keyAssignmentWeight[i].freeWeight));
    seen[var(p)] = 1;
    if (coresOfVar[v].size() == 0) varsInCores.push(v);
    coresOfVar[v].push(coreid);
  }

  // [TODO: incremental] Copy all the soft literals from the subcores into the
  // new core.
  for (int i = 0; i < subCores.size(); i++) {
    LocalCore &subcore = localCores[subCores[i]];
    for (int j = 0; j < subcore.coreLits.size(); j++) {
      Lit p = subcore.coreLits[j].lit;
      Var v = var(p);
      if (!seen[v]) {
        core.coreLits.push(subcore.coreLits[j]);
        seen[v] = 1;
        if (coresOfVar[v].size() == 0) varsInCores.push(v);
        coresOfVar[v].push(coreid);
      } else {
        for (int k = 0; k < core.coreLits.size(); k++)
          if (core.coreLits[k].lit == p)
            core.coreLits[k].weight += subcore.coreLits[j].weight;
      }
    }
  }

  // Clear seen for the next analysis new core.
  assert(falseVar == var_Undef || seen[falseVar]);
  for (int i = 0; i < core.coreLits.size(); i++)
    seen[var(core.coreLits[i].lit)] = 0;

  // Update the related information of the new core and some global infos.
  core.weight = minWeight + subcoresWeightSum;
  assert(core.weight > 0);
  lookaheadConflictCost += core.weight;
  assert(lookaheadConflictCost > prevLaConflictCost);
  nonInferenceCost += core.weight;
  core.falsifiedWeight = 0;
  core.seen = false;
  core.unlockedIndex = -1;

  LAM_PRINT(LOOKAHEAD, "c set core %d, weight %" PRId64 ": ", coreid,
            core.weight);
  for (int i = 0; i < core.coreLits.size(); i++) {
    if (core.coreLits[i].weight > weightsBckp[var(core.coreLits[i].lit)])
      LAM_PRINT(LOOKAHEAD,
                "c coreid %d, lit %d, weight %" PRId64 ", weightsBckp %" PRId64
                " \n",
                coreid, toInt(core.coreLits[i].lit), core.coreLits[i].weight,
                weightsBckp[var(core.coreLits[i].lit)]);
    assert(core.coreLits[i].weight <= weightsBckp[var(core.coreLits[i].lit)] &&
           core.coreLits[i].weight > 0);
    LAM_PRINT(LOOKAHEAD, "%d(%" PRId64 "),", toInt(core.coreLits[i].lit),
              core.coreLits[i].weight);
  }
  LAM_PRINT(LOOKAHEAD, "\n");
}

void Solver::setCore(int coreid, int64_t coreCost) {
  LocalCore &core = localCores[coreid];

  core.weight = core.coreLits[0].weight;
  for (int i = 0; i < core.coreLits.size(); i++)
    if (core.weight > core.coreLits[i].weight)
      core.weight = core.coreLits[i].weight;

  for (int i = 0; i < core.coreLits.size(); i++) {
    Var v = var(core.coreLits[i].lit);
    if (coresOfVar[v].size() == 0) varsInCores.push(v);
    coresOfVar[v].push(coreid);
    assert(core.coreLits[i].weight == weights[v] && weights[v] >= 0 &&
           weights[v] <= weightsBckp[v]);
    core.coreLits[i].weight = core.weight;
    // Core lit should always be postive.
    assert(softLits[v] == core.coreLits[i].lit);
    weights[v] -= core.weight;
    hardenHeap.update(v);
    orderHeapLookahead.update(v);
    if (weights[v] > 0) {
      lastConflLits.update(v);
    }
  }
  assert(core.weight > 0);
  nonInferenceCost += core.weight;
  lookaheadConflictCost += core.weight;
  avgCoreWeight.put(core.weight);
  avgCoreSize.put(core.coreLits.size());

  activeCores.push(coreid);
}

void Solver::recoverAffectedCoresAfterLookahead(int skipCoreId) {
  for (int i = 0; i < affectedCores.size(); i++) {
    int coreid = affectedCores[i];
    if (skipCoreId != -1 && coreid == skipCoreId) continue;
    localCores[coreid].falsifiedWeight = 0;
    localCores[coreid].unlockedIndex = -1;
  }

  affectedCores.clear();
  for (int i = 0; i < unlockedVars.size(); i++)
    unlockCoreOfVar[unlockedVars[i]] = -1;
  unlockedVars.clear();
}

void Solver::setNewcoreReason(int coreid) {
  LocalCore &core = localCores[coreid];
  core.reasons.clear();
  int lvl = 0;  // The largets decision level in reason.
  for (int i = 0; i < newcoreReason.size(); i++) {
    core.reasons.push(newcoreReason[i]);
    Var v = var(newcoreReason[i]);
    seen[v] = 1;
    if (level(v) > lvl) {
      lvl = level(v);
    }
  }
  for (int i = 0; i < subCores.size(); i++) {
    LocalCore &subcore = localCores[subCores[i]];
    for (int j = 0; j < subcore.reasons.size(); j++) {
      if (!seen[var(subcore.reasons[j])]) {
        core.reasons.push(subcore.reasons[j]);
        Var v = var(subcore.reasons[j]);
        seen[v] = 1;
        if (level(v) > lvl) {
          lvl = level(v);
        }
      }
    }
  }
  core.level = lvl;

  for (int i = 0; i < core.reasons.size(); i++) {
    seen[var(core.reasons[i])] = 0;
  }
}

void Solver::cleanSubcores() {
  if (subCores.size() == 0) return;

  int i, j, k;
  for (i = 0, j = 0; i < activeCores.size(); i++) {
    int coreId = activeCores[i];
    if (!localCores[coreId].seen)
      activeCores[j++] = coreId;
    else
      lastCores.push(coreId);
  }
  activeCores.shrink(i - j);

  for (i = 0; i < subCores.size(); i++) {
    int subCoreId = subCores[i];
    LocalCore &subCore = localCores[subCoreId];
    subCore.seen = false;
    for (j = 0, k = 0; j < subCore.coreLits.size(); j++) {
      Var v = var(subCore.coreLits[j].lit);
      for (k = 0; k < coresOfVar[v].size(); k++) {
        if (coresOfVar[v][k] != subCoreId) continue;
        while (k < coresOfVar[v].size() - 1) {
          coresOfVar[v][k] = coresOfVar[v][k + 1];
          k++;
        }
      }
      coresOfVar[v].shrink(1);
    }
  }
  subCores.clear();
}

void Solver::setCoreMultilock(int coreid) {
  assert(subCores.size() > 0);
  setLitWeightBeforeCancelAssignment(coreid);
  recoverAffectedCoresAfterLookahead(coreid);
  setNewcoreReason(coreid);
  cleanSubcores();
  activeCores.push(coreid);
  LocalCore &core = localCores[coreid];
  avgCoreWeight.put(core.weight);
  avgCoreSize.put(core.coreLits.size());

  LAM_PRINT(LOOKAHEAD, "active cores: ");
  for (int i = 0; i < activeCores.size(); i++)
    LAM_PRINT(LOOKAHEAD, "%d,", activeCores[i]);
  LAM_PRINT(LOOKAHEAD, "\n\n");

  LOOKAHEAD_MULTILOCKS_MULTICORES++;
}

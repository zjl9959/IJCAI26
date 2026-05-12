#include <iomanip>
#include <iostream>

#include "core/Solver.h"
#include "utils/System.h"

using namespace Minisat;
using namespace std;

template <typename A, typename B>
double safeDivide(A a, B b) {
  if (b == 0) {
    return 0.0;
  }
  return (double)a / (double)b;
}

void Solver::printSummaryStat() {
  double cpu_time = cpuTime();
  double mem_used = memUsedPeak();
  int dynamic_vars = nVars() - staticNbVars;

  double softConflRate = safeDivide(softConflicts, conflicts) * 100.0;
  double lk_succ_rate = safeDivide(nbLKsuccess, LOOKAHEAD) * 100.0;
  double lk_prop_rate = safeDivide(lk_propagations, propagations) * 100.0;
  double rand_dec_rate = safeDivide(rnd_decisions, decisions) * 100.0;
  double del_conf_lits_rate =
      safeDivide(max_literals - tot_literals, max_literals) * 100.0;
  double s_prop_rate = safeDivide(s_propagations, propagations) * 100.0;
  double mult_lk_succ_rate =
      safeDivide(LOOKAHEAD_MULTILOCKS_SUCCS, LOOKAHEAD_MULTILOCKS) * 100.0;

  double mult_cores_ratio =
      safeDivide(LOOKAHEAD_MULTILOCKS_MULTICORES, LOOKAHEAD_MULTILOCKS);
  double conflicts_per_sec = safeDivide(conflicts, cpu_time);
  double decisions_per_sec = safeDivide(decisions, cpu_time);
  double propagations_per_sec = safeDivide(propagations, cpu_time);
  double avg_conf_len = safeDivide(tot_literals, conflicts);
  double avg_soft_conf_len = safeDivide(softLiterals, softConflicts);
  double avg_hard_conf_len =
      safeDivide(tot_literals - softLiterals, conflicts - softConflicts);

  // Set the decimal precision to 2
  cout << std::fixed << setprecision(2);

  cout << "c nbLK: " << LOOKAHEAD << ", nbSuccLK: " << nbLKsuccess << "("
       << lk_succ_rate << "%), nbLKup: " << lk_propagations << "("
       << lk_prop_rate << "%), hardens " << nbHardens << " (fixed "
       << fixedByHardens << "), dynVars " << dynamic_vars
       << ", shorten: " << nbSavedLits << endl;

  cout << "c restarts              : " << starts << endl;
  cout << "c conflicts             : " << conflicts << " (" << conflicts_per_sec
       << " /sec)" << endl;
  cout << "c decisions             : " << decisions << " (" << rand_dec_rate
       << "% random) (" << decisions_per_sec << " /sec)" << endl;
  cout << "c propagations          : " << propagations << " ("
       << propagations_per_sec << " /sec)" << endl;
  cout << "c conflict literals     : " << tot_literals << " ("
       << del_conf_lits_rate << "% deleted)" << endl;
  cout << "c Memory used           : " << mem_used << " MB" << endl;
  cout << "c CPU time              : " << cpu_time << " s" << endl;
  cout << "c nbSimplifyAll         : " << nbSimplifyAll << endl;
  cout << "c s_propagations        : " << s_propagations << endl;
  cout << "c s_cost_ratio          : " << s_prop_rate << "%" << endl;
  cout << "c nbGrbgCllct           : " << nbGrbgCllct << endl;
  cout << "c LA cost without inference: " << nonInferenceCost << endl;
  cout << "c LA cost update        : " << updateCost << endl;
  cout << "c LA execution          : " << LOOKAHEAD << " (" << nbLKsuccess
       << " succs (" << lk_succ_rate << "%)) (" << REDO_LOOKAHEAD << " redo)"
       << endl;
  cout << "c LAM execution         : " << LOOKAHEAD_MULTILOCKS << " ("
       << LOOKAHEAD_MULTILOCKS_SUCCS << " succs (" << mult_lk_succ_rate
       << "%)) (" << LOOKAHEAD_MULTILOCKS_MULTICORES << " cores found ("
       << mult_cores_ratio << ")) (" << LOOKAHEAD_MULTILOCKS_SKIP << " skip)"
       << endl;
  cout << "c SLA time              : " << SECOND_LOOKAHEAD_TIME << " s" << endl;
  cout << scientific << setprecision(4);
  cout << "c lk_ticks              : " << static_cast<double>(lk_ticks) << endl;
  cout << "c s_ticks               : " << static_cast<double>(s_ticks) << endl;
  cout << "c ticks                 : " << static_cast<double>(ticks) << endl;

#ifdef printBackWardSubsumeData
  float rate1, rate2;
  if (allsbsm == 0) {
    rate1 = 0;
    rate2 = 0;
  } else {
    rate1 = (float)(sbsmTtlg) / (allsbsm);
    rate2 = (float)(sbsmAbsFail) / (allsbsm);
  }
  cout << "c allsbsm              : " << allsbsm << ", sbsmTtlg " << sbsmTtlg
       << "(" << rate1 << "), sbsmAbsFail " << sbsmAbsFail << "(" << rate2
       << "), smeq " << smeq << ", sbsmTime " << totalsbsmTime << " s, s_ticks "
       << s_ticks << endl;
#endif

  // Print formatted statistics for better future analysis.
  cout << "c Formatted Statistics: ";
  cout << "restarts=" << starts << " ";
  cout << "conflicts=" << conflicts << " ";
  cout << "soft_conf=" << softConflicts << " ";
  cout << "soft_conf(%)=" << softConflRate << " ";
  cout << "hard_conf=" << conflicts - softConflicts << " ";
  cout << "hard_conf(%)=" << 100.0 - softConflRate << " ";
  cout << "conf_lits=" << tot_literals << " ";
  cout << "soft_lits=" << softLiterals << " ";
  cout << "hard_lits=" << tot_literals - softLiterals << " ";
  cout << "avg_conf_len=" << avg_conf_len << " ";
  cout << "avg_s_conf_len=" << avg_soft_conf_len << " ";
  cout << "avg_h_conf_len=" << avg_hard_conf_len << " ";
  cout << "decisions=" << decisions << " ";
  cout << "propagations=" << propagations << " ";
  cout << "hardens_num=" << nbHardens << " ";
  cout << "hardens_fixed=" << fixedByHardens << " ";
  cout << "dynVars=" << dynamic_vars << " ";
  cout << "CPU_time=" << cpu_time << " ";
  cout << "Mem_used=" << mem_used << " ";
  cout << "nb_simp=" << nbSimplifyAll << " ";
  cout << "s_prop=" << s_propagations << " ";
  cout << "s_prop(%)=" << s_prop_rate << " ";
  cout << "nbGrbgCllct=" << nbGrbgCllct << " ";
  cout << "LA_num=" << LOOKAHEAD << " ";
  cout << "LA_succs=" << nbLKsuccess << " ";
  cout << "LA_succ(%)=" << lk_succ_rate << " ";
  cout << "LA_redo=" << REDO_LOOKAHEAD << " ";
  cout << "LA_prop=" << lk_propagations << " ";
  cout << "LA_prop(%)=" << lk_prop_rate << " ";
  cout << "LAM_num=" << LOOKAHEAD_MULTILOCKS << " ";
  cout << "LAM_succs=" << LOOKAHEAD_MULTILOCKS_SUCCS << " ";
  cout << "LAM_succ(%)=" << mult_lk_succ_rate << " ";
  cout << "LAM_cores=" << LOOKAHEAD_MULTILOCKS_MULTICORES << " ";
  cout << "LAM_cores_rat=" << mult_cores_ratio << " ";
  cout << "LAM_skip=" << LOOKAHEAD_MULTILOCKS_SKIP << " ";
  cout << "LAM_time=" << SECOND_LOOKAHEAD_TIME << " ";
  cout << "lk_ticks=" << static_cast<double>(lk_ticks) << " ";
  cout << "s_ticks=" << static_cast<double>(s_ticks) << " ";
  cout << "ticks=" << static_cast<double>(ticks) << " ";
  cout << "avg_core_weight=" << avgCoreWeight.mean() << " ";
  cout << "avg_core_size=" << avgCoreSize.mean() << " ";
  cout << "core_num=" << avgCoreSize.count() << " ";
  cout << "cores_hard_conf=" << numCoresHardConflict << " ";
  cout << "cores_false_var=" << numCoresFalseVar << " ";
  cout << "cores_false_core=" << numCoresFalseCore << " ";
  cout << endl;

  // Reset to default floating-point formatting.
  cout << defaultfloat;
}

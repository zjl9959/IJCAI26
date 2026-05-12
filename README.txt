The supplementary material provides four variants described in the paper.
  The "bins" folder containing statically linked executables that can run directly in a Linux environment.
  The "codes" folder containing the source code for the corresponding versions.

For the baseline version of WMaxCDCL and the compared solvers,
we downloaded them from the MaxSAT Evaluation website.

The links are listed below:

  WMaxCDCL: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/WMaxCDCL2024.zip
  Open-WBO: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/unweighted/OpenWBO.zip
  Pacose: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/Pacose24.zip
  CGSS2: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/CGSS2.zip
  UwrMaxSAT: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/UWrMaxSat-SCIP.zip
  EvalMaxSAT: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/EvalMaxSAT_2024.zip
  CASHWMaxSAT: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/CASHWMaxSAT-DisjCom-S6.zip

The configurations to test these solvers are listed below:

  WMaxCDCL: > bin/wmaxcdcl_static $wcnf_file_path
  Open-WBO: > bin/open-wbo $wcnf_file_path
  Pacose: > bin/Pacose $wcnf_file_path
  CGSS2: > bin/cgss2 $wcnf_file_path
  UwrMaxSAT: > bin/uwrmaxsat -no-scip -v0 -no-sat -no-par -m -bm $wcnf_file_path
  EvalMaxSAT: > bin/EvalMaxSAT --noSaveCores --noSimplify --TCT 5000 --timeSCIP 0 $wcnf_file_path
  CASHWMaxSAT: > bin/cashwmaxsat-disjcom -v0 -no-bin -no-sat -m -bm -no-par -no-scip $wcnf_file_path

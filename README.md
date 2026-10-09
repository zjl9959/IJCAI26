# Weight-Aware Branch-and-Bound for Weighted Maximum Satisfiability

The supplementary material provides four variants described in this IJCAI [paper](https://www.ijcai.org/proceedings/2026/270), for reproducibility checking.

## Proposed Variants

### Executable

The `bins` folder contains four statically linked executables that can be executed directly in a Linux environment with this command:

```shell
  ./bins/$variant_solver $inst_file_path
```

### Source Code

The `codes` folder contains the source code for the corresponding versions.

### Build on Linux

To build a variant from source code on a Linux machine, please follow these steps:

1. Environment setup:
   - Please use a Linux machine with **GCC compiler 15.2.0** or a newer version.
   - Ensure your system has the **statically linked version** of the C++ standard library (**libstdc++.a**) and the zlib development tool (**libz.a**) installed.
     > For example, in a Debian or Ubuntu system, install libstdc++.a and libz.a with this command: `sudo apt-get install build-essential zlib1g-dev`

2. Build the source code with this command:

   ```shell
   cd codes/$variant_folder/simp && make rs
   ```

   The generated binary is called `wmaxcdcl_static` under the `codes/$variant_folder/simp` folder.

### Build on MacOS

Static linking is unsupported on macOS; however, dynamic linking is supported. To build a dynamically linked variant from source on macOS, execute the following command:

```shell
cd codes/$variant_folder/simp && make
```

The generated binary is called `wmaxcdcl` under the `codes/$variant_folder/simp` folder.

## Compared Solvers

For the baseline version of WMaxCDCL and the compared solvers, we downloaded them from the MaxSAT Evaluation [website](https://maxsat-evaluations.github.io/).

The links are listed below:

+ WMaxCDCL: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/WMaxCDCL2024.zip
+ Open-WBO: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/unweighted/OpenWBO.zip
+ Pacose: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/Pacose24.zip
+ CGSS2: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/CGSS2.zip
+ UwrMaxSAT: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/UWrMaxSat-SCIP.zip
+ EvalMaxSAT: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/EvalMaxSAT_2024.zip
+ CASHWMaxSAT: https://maxsat-evaluations.github.io/2024/mse24-solver-src/exact/weighted/CASHWMaxSAT-DisjCom-S6.zip

The configurations to test these solvers are listed below:

+ WMaxCDCL: > bin/wmaxcdcl_static $wcnf_file_path
+ Open-WBO: > bin/open-wbo $wcnf_file_path
+ Pacose: > bin/Pacose $wcnf_file_path
+ CGSS2: > bin/cgss2 $wcnf_file_path
+ UwrMaxSAT: > bin/uwrmaxsat -no-scip -v0 -no-sat -no-par -m -bm $wcnf_file_path
+ EvalMaxSAT: > bin/EvalMaxSAT --noSaveCores --noSimplify --TCT 5000 --timeSCIP 0 $wcnf_file_path
+ CASHWMaxSAT: > bin/cashwmaxsat-disjcom -v0 -no-bin -no-sat -m -bm -no-par -no-scip $wcnf_file_path

## Citation

If you find this code or our paper useful for your research, please cite our work:

```bibtex
@inproceedings{ijcai2026p270,
  title     = {Weight-Aware Branch-and-Bound for Weighted Maximum Satisfiability},
  author    = {Zhang, Jialu and Li, Chu-Min and Cherif, Sami and Li, Shuolin},
  booktitle = {Proceedings of the Thirty-Fifth International Joint Conference on
               Artificial Intelligence, {IJCAI-26}},
  publisher = {International Joint Conferences on Artificial Intelligence Organization},
  editor    = {Diego Calvanese},
  pages     = {2427--2436},
  year      = {2026},
  month     = {8},
  note      = {Main Track},
  doi       = {10.24963/ijcai.2026/270},
  url       = {https://doi.org/10.24963/ijcai.2026/270},
}

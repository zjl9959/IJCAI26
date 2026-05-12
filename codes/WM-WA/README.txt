1. Environment setup:

    a. Please use a Linux machine with GCC compiler 12.2.0 or a newer vresion.

    b. Ensure your system has the statically linked version of the C++ standard library (libstdc++.a) installed. 
       For example in Debian / Ubuntu system, install libstdc++.a with this command:

            > sudo apt-get install build-essential


2. Please build the source code with this command:

    > cd simp && make rs

    The output binary is called "wmaxcdcl_static".


3. Execute the binary with this command:

    > ./wmaxcdcl_static <parameters> $wcnf_file_path

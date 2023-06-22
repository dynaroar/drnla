# DrNLA: Extending Verification to Non-linear Programs through Dual Re-writing

DrNLA is a hybrid analysis tool to synthesis linear conditions for nonlinear branching programs. In this released repository, core files are summarized as following:

`Dependencies`
- `dyn_instr source`: C transformation (Our Ocaml command line application).
- `dig`: Dynamic learning engine DIG, getting source [here](https://github.com/dynaroars/dig).
- `Ultimate-linux`: Static analysis framework, getting source [here](https://github.com/ultimate-pa/ultimate).

`Source Code` (main algorithm)
- `drnla.py`: DrNLA driver file.
- `analysis.py`: Dual refinement algorithm.
- `dynamic.py`: Dynamic learning.
- `static.py`: Static validation.
- `solver.py`: SMT solver, constraints solving related.
- `transform.py`: Setup for C transformation.
- `ultils/*`: Environment setting up and other utilities.

`Benckmarks`
- `ctl-svcomp`: Branching time properties with nonlinear behaviors, C source code, T2 versions, and FuncTion versions.
- `ctl-pldi13-nla`: Various CTL properties with NLA version, T2 versions, and FuncTion versions.
- `ctl-pldi13-nlas`: Various type of NLAs , T2 versions, and FuncTion versions.
- `ctl-multi`: Customized NLA benchmarks, T2 versions, and FuncTion versions.

### Building DrNA

`DrNLA` in built on top of open source dynamic analysis engine and static analysis framework, following instructions below to setup the running environment.
Install general dependencies:

```
pip3 install lark z3
sudo cpan -i Time::Out
sudo cpan -i YAML::Tiny
```

#### Build Instrumentation for C Program
`dyn_instr` is our Ocaml application for program transformation, it is required for both dynamic and static analysis (alternatively we [released](https://github.com/dynaroar/drnla/releases) the binary).
```
git clone git@github.com:dynaroar/drnla.git
git submodule update --init
# inside dun_instr directory
opam init
opam switch create 4.05.0
opam install dune cil num csv ocamlbuild ocamlfind menhir
cd deps/dyn_instr
dune build src/instr.exe
```

#### Install Dynamic and Static Analysis Tools
Our algorithm uses two open source projects `DIG` and `UAutomizer` (mentioned in previous section), if you would like to install dependencies as your preference, setup environment variables:

```
export CONDA_HOME="/tools/miniconda3/bin/python3" //skip if your local python3 verison >= 3.9.5
export DIG_HOME="/tools/dig/src/dig.py"
export ULTIMATE_HOME="/path/to/ultimate/releaseScripts/default/UAutomizer-linux" //defualt is in deps/UAutomizer-linux
```
Otherwise you can install them to default directory: 
- Install Ultimate to `drnla/deps/UAutomizer-linux`, refer to [build](https://github.com/ultimate-pa/ultimate/wiki/Usage) (for convenience we provide the compiled version used in our experiments).
- Install DIG to `drnla/deps/dig`, refer to [dockfile](https://github.com/dynaroars/dig/blob/4ee9b94ed1117db312cb5eeb305c710809e0a7f8/Dockerfile).  
<!-- - copy `scripts/*` to `/usr/local/bin` (or somewhere in your PATH) -->
<!-- - `git submodule update --init` -->

### Build and Setup Verifiers
We provide a command-line script for testing and CTL verification experiments with different CTL verifiers, summarized as following (checkout [released](https://github.com/dynaroar/drnla/releases) package for their binaries in case you would have trouble building them from the source): 

- Install [T2](https://github.com/mmjb/T2#readme) to `drnla/deps/`, built with gcc-5 and g++5 version.
- Install [FuncTion](https://github.com/caterinaurban/function) to `drnla/deps`, for more information, refer to [homepage](https://caterinaurban.github.io/project/function/), built with Ocaml `4.03.0`, `3.12.1`.

```
# docker run -t -i -v ~/dynamiteLTL/deps/function:/home/test/function function /bin/bash
# Running command example for `FucnTion` and `T2`
./function tests/ctl/or_test.c -ctl "AX{x==0}" -precondition "x == 1" -domain polyhedra
# T2 command
mono src/bin/Debug/T2.exe -input_t2 test/ax_test_2.t2 -CTL "[AG](p <= 0 || [AX](p <= 0))"
```

### Running DrNLA

You don't need any CTL veifiers to run DrNLA, as the current version only supports the synthesis and program rewriting, following is a command-line running example for C program.
```
# from DrNLA root directory
$ cd src/
$ ./drnla.py --inp <filename> --refine [k] --prop []
// e.g. ./drnla.py --inp ../test-tmp/ex3/ex3.c --init --snaps 500 
./drnla.py --inp ../test-tmp/ex3/ex3.c --init --refine 4 --prop 'reach'
```
Other options:

 ```
usage: drnla [-h] [--inp INP] [--init-ou] [--bv] [--log {0,1,2,3,4}] [--timeout TIMEOUT] [--refine REFINE] [--snaps SNAPS] [--repeat REPEAT] [--upper UPPER]
             [--lbnd [LBND]] [--prop {reach,termination,ltl,ctl}] [--verdict VERDICT] [--tmpdir TMPDIR]
DrNLA
optional arguments:
  -h, --help            show this help message and exit
  --inp INP, -i INP     input c program
  --init-ou, -init      initial OU mapping for IF ELSE
  --bv, -bv             flag to run initial dynamic analysis on the input directly
  --log {0,1,2,3,4}, -log {0,1,2,3,4}
                        set logger level info
  --timeout TIMEOUT, -timeout TIMEOUT
                        set timeout (s)
  --refine REFINE, -refine REFINE
                        set the number of refinement iteration
  --snaps SNAPS, -snaps SNAPS
                        set the number of snaps/model in cex generalization
  --repeat REPEAT, -repeat REPEAT
                        set the repeat bound for the same variable sanp
  --upper UPPER, -upper UPPER
                        set the upper bound for normalized template invriants
  --lbnd [LBND], -lbnd [LBND]
                        set loop bound for non-terminating loop
  --prop {reach,termination,ltl,ctl}, -prop {reach,termination,ltl,ctl}
                        select which property to verify
  --verdict VERDICT, -verdict VERDICT
                        user provided desired IF condition
  --tmpdir TMPDIR, -tmpdir TMPDIR
                        set temporary path for intermediate files
 ```

### Benchmarking and Testing with DrNLA 

Inside `benchmarks` directory, we provide a script to run various tools on all the benchmark sets.
1. Execute the benchmarks:
```
# ./run [benchamrks] run [tool-name: t2 | ddr | function | ultimate]
# P.S. ddr is a shortcut to run DrNLA in the script
./run nla-term run ddr
# results will be saved in <tmpfolder>
```
2. Collect the results:
```
./harvest nocsvs nla-term <tmpfolder>
```
3. All the results will be written into latex tables, recording time, synthesis resutls and verification results. For each run, the intermediate results of DrNLA will also be saved into your home temporary directory, `Path().home()/$tmp` (create one if it doesn't exist).

Finally, feel free to open an [issue](https://github.com/cyruliu/drnla/issues) ticket if you have any questions.


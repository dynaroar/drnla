# Dynamic Proofs of LTL

```
pip3 install lark z3
sudo cpan -i Time::Out
sudo cpan -i YAML::Tiny
```

### Installation

#### Instrumentation

```
opam init
opam switch create 4.05.0
opam install dune cil num csv ocamlbuild ocamlfind menhir
cd deps/dyn_instr
dune build src/instr.exe
```

#### Install dynamic and static analysis tools

 * Install Ultimate to `/tools/ultimate`
 * Install DIG to `/tools/dig`, refer to [dockfile](https://github.com/dynaroars/dig/blob/4ee9b94ed1117db312cb5eeb305c710809e0a7f8/Dockerfile)  
 * copy `scripts/*` to `/usr/local/bin` (or somewhere in your PATH)
 * `git submodule update --init`

If you would like to install dependencies as your prefernce, setup environment veriables:

```
export CONDA_HOME="/tools/miniconda3/bin/python3"
export DIG_HOME="/tools/dig/src/dig.py"
export ULTIMATE_HOME="/path/to/ultimate/releaseScripts/default/UAutomizer-linux"

```

### Usage


```
  $ cd src/
  $ dynamltl.py --inp <filename> 
```

### Benchmarks

1. Execute the benchmarks:
```
DYNAMITE_HOME=/tools/ DYNAMITE_DEPS=/tools/ ./run nla-term run ultimate
# results will be saved in <tmpfolder>
```
2. Collect the results:
```
./harvest nocsvs nla-term <tmpfolder>
```

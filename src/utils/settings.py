from pathlib import Path
from functools import partial
import os

LoggerLevel = 4
GenTcs = False
Tmpdir = Path().home()/'tmp'
TimeOut =  5 * 1000
RefineBound = 1

SrcDir = Path(__file__).parent
DynLTLDir = Path(__file__).parent.parent.parent
DigPython = Path().home()/'miniconda3/bin/python3'

DigPy = DynLTLDir/'deps/dig/src/dig.py'
UltimateHome = Path().home()/'Downloads/ultimate/releaseScripts/default/UAutomizer-linux'

class Cil:
    trans_dir = DynLTLDir / 'deps' / 'dyn_instr'
    assert trans_dir.is_dir(), trans_dir

    cil_exe = trans_dir / f'{trans_dir}/_build/default/src/instr.exe'
    dcmd = partial('{exe} -dig -nopre {inp}'.format, exe=cil_exe)
    scmd = partial('{exe} -val {inp} -inv {invars}'.format, exe=cil_exe)
    dtrans = lambda inp: Cil.dcmd(inp=inp)
    strans = lambda inp, invars: Cil.scmd(inp=inp, invars=invars)

 # with running file
# ~/miniconda3/bin/python3 -O src/dig.py ~/tmp/poly2/poly2-case1-2.csv --noss --nocongruences --noeqts --nominmaxplus --maxdeg 1 --log_level 4 --writeresults ~/tmp/poly2/poly2-case1-2.v --writevtraces ~/tmp/poly2/poly2-case1-2.tmp.csv

class Dynamic:
    dig_flags = '--noss --nocongruences --noeqts --nominmaxplus --maxdeg 1 --log_level 4'
    source_opts = '{python} -O {dig_py} {source} {flags} --writeresults {invars_file} --writevtraces {vtrace_file}'
    trace_opts = '{python} -O {dig_py} {source} {flags} --writeresults {invars_file}'
    source_cmd = partial(source_opts.format, python=DigPython, dig_py=DigPy, flags=dig_flags)
    trace_cmd = partial(trace_opts.format, python=DigPython, dig_py=DigPy, flags=dig_flags)
    source_run = lambda inp, invars, vtrace: Dynamic.source_cmd(source=inp, invars_file=invars, vtrace_file=vtrace)
    vtrace_run = lambda inp, invars: Dynamic.trace_cmd(source=inp, invars_file=invars)
      
# ./run-ultimate.sh -tc config/AutomizerLTL.xml -s config-poly/svcomp-LTL-64bit-Automizer_Default.epf -i ~/dynamic-ltl/dynamiteLTL/benchmarks/polynomials/poly2.c
# ./run-ultimate.sh -s config/svcomp-Reach-64bit-Automizer_Default.epf -tc config/AutomizerReach.xml -i ~/dynamic-ltl/dynamiteLTL/benchmarks/polynomials/poly2-case8-i1.c    
# java \
# -Dosgi.configuration.area=config/ \
# -Xmx10G \
# -Xss4m \
# -jar $ultimatePath/plugins/org.eclipse.equinox.launcher_1.5.800.v20200727-1323.jar \
# -data config/data \
class Static:
    java_ultimate = f'java -Dosgi.configuration.area=config -Xmx10G -Xss4m -jar {UltimateHome}/plugins/org.eclipse.equinox.launcher_1.5.800.v20200727-1323.jar -data config/data'
    ultimate_bash = UltimateHome / 'run-ultimate.sh'
    reach_toolchain = UltimateHome / 'config/AutomizerReach.xml'
    reach_setting = UltimateHome / 'config/svcomp-Reach-64bit-Automizer_Default.epf'
    ultimate_cmd = "{run_ultimate} -tc {toolchain} -s {setting} -i {filename}"
    # run_cmd = partial(ultimate_cmd.format, run_ultimate=ultimate_bash, toolchain=reach_toolchain, setting=reach_setting)
    run_cmd = partial(ultimate_cmd.format, run_ultimate=java_ultimate, toolchain=reach_toolchain, setting=reach_setting)
    run = lambda source: Static.run_cmd(filename=source)
 
class Ctrace:
    SE_MIN_DEPTH = 20

    GCC_CMD = "gcc"
    COMPILE = "{gcc} {filename} -o {tmpfile}"
    COMPILE = partial(COMPILE.format, gcc=GCC_CMD)
    C_RUN = "./{exe} > {tracefile}"
    C_RUN = partial(C_RUN.format)

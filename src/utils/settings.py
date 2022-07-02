from pathlib import Path
from functools import partial
import os

logger_level = 4
gen_tcs = False
init_ou = False
is_lbnd = False
tmpdir = Path().home()/'tmp'
timeout = 600
refine = 4
snaps = 1000
repeat = 50
upper = 20
lbnd = 500
prop = 'termination'
props_list = ['reach','termination', 'ltl', 'ctl']
verdict = '1==1'

SrcDir = Path(__file__).parent
DrNLADir = Path(__file__).parent.parent.parent
   
class Cil:
    trans_dir = DrNLADir/'deps'/'dyn_instr'
    assert trans_dir.is_dir(), trans_dir

    cil_exe = trans_dir / f'{trans_dir}/_build/default/src/instr.exe'
    dcmd = partial('{exe} -dig -nopre {inp}'.format, exe=cil_exe)
    dcmdl = partial('{exe} -dig -nopre {inp} -lbnd {lbnd}'.format, exe=cil_exe)
    scmd = partial('{exe} -val {inp} -inv {invars}'.format, exe=cil_exe)
    vcmd = partial('{exe} -val {inp} -inv {invars} -pre {pre} -case {case}'.format, exe=cil_exe)
    lcmd = partial('{exe} -lia {ous} {inp}'.format, exe=cil_exe)

    dtrans = lambda inp: Cil.dcmd(inp=inp)
    dtransl = lambda inp, bnd: Cil.dcmdl(inp=inp, lbnd=bnd)
    strans = lambda inp, invars: Cil.scmd(inp=inp, invars=invars)
    vtrans = lambda inp, invars, pre, case: Cil.vcmd(inp=inp, invars=invars, pre = pre, case=case)
    ltrans = lambda inp, ouf: Cil.lcmd(inp=inp, ous=ouf)

 # with running file
# ~/miniconda3/bin/python3 -O src/dig.py ~/tmp/poly2/poly2-case1-2.csv --noss --nocongruences --noeqts --nominmaxplus --maxdeg 1 --log_level 4 --writeresults ~/tmp/poly2/poly2-case1-2.v --writevtraces ~/tmp/poly2/poly2-case1-2.tmp.csv

class Dynamic:
    if 'CONDA_HOME' in os.environ:
        DigPython = Path(os.getenv('CONDA_HOME'))
    else:
        # DigPython = Path().home()/'miniconda3/bin/python3'
        DigPython = 'python3'
    if 'DIG_HOME' in os.environ:
        DigPy = Path(os.getenv('DIG_HOME'))
    else:
        DigPy = DrNLADir/'deps/dig/src/dig.py'
 
    dig_flags = '--noss --nocongruences --nominmaxplus --maxdeg 1 --log_level 4'
    source_opts = '{python} -O {dig_py} {source} {flags} --writeresults {invars_file} --writevtraces {vtrace_file}'
    trace_opts = '{python} -O {dig_py} {source} {flags} --writeresults {invars_file}'
    source_cmd = partial(source_opts.format, python=DigPython, dig_py=DigPy, flags=dig_flags)
    trace_cmd = partial(trace_opts.format, python=DigPython, dig_py=DigPy, flags=dig_flags)
    source_run = lambda inp, invars, vtrace: Dynamic.source_cmd(source=inp, invars_file=invars, vtrace_file=vtrace)
    vtrace_run = lambda inp, invars: Dynamic.trace_cmd(source=inp, invars_file=invars)
      

class Static:
    if 'ULTIMATE_HOME' in os.environ:
        StaticHome = Path(os.getenv('ULTIMATE_HOME'))
    else:
        StaticHome = DrNLADir / 'deps' / 'UAutomizer-linux'

    java_ultimate = f'java -Dosgi.configuration.area=config -Xmx10G -Xss4m -jar {StaticHome}/plugins/org.eclipse.equinox.launcher_1.5.800.v20200727-1323.jar -data config/data'
    ultimate_bash = StaticHome / 'run-ultimate.sh'

    reach_toolchain = StaticHome / 'config/AutomizerReach.xml'
    reach_setting = StaticHome / 'config/svcomp-Reach-64bit-Automizer_Default.epf'

    term_toolchain = StaticHome / 'config/AutomizerTermination.xml'
    term_setting = StaticHome / 'config/svcomp-Termination-64bit-Automizer_Default.epf'
    
    ltl_toolchain = StaticHome / 'config/AutomizerLTL.xml'
    ltl_setting = StaticHome / 'config/svcomp-LTL-64bit-Automizer_Default.epf'

    ultimate_cmd = "{run_ultimate} -tc {toolchain} -s {setting} -i {filename} --core.toolchain.timeout.in.seconds {time_out}"
     
    # run_cmd = partial(ultimate_cmd.format, run_ultimate=ultimate_bash, toolchain=reach_toolchain, setting=reach_setting)
    run_rcmd = partial(ultimate_cmd.format, run_ultimate=java_ultimate, toolchain=reach_toolchain, setting=reach_setting, time_out=timeout)
    run_tcmd = partial(ultimate_cmd.format, run_ultimate=java_ultimate, toolchain=term_toolchain, setting=term_setting, time_out=timeout)
    run_lcmd = partial(ultimate_cmd.format, run_ultimate=java_ultimate, toolchain=ltl_toolchain, setting=ltl_setting, time_out=timeout)
    
    run_reach = lambda source: Static.run_rcmd(filename=source)
    run_term = lambda source: Static.run_tcmd(filename=source)
    run_ltl = lambda source: Static.run_lcmd(filename=source)
 
class Ctrace:
    SE_MIN_DEPTH = 20

    GCC_CMD = "gcc"
    COMPILE = "{gcc} {filename} -o {tmpfile}"
    COMPILE = partial(COMPILE.format, gcc=GCC_CMD)
    C_RUN = "./{exe} > {tracefile}"
    C_RUN = partial(C_RUN.format)

from pathlib import Path
from functools import partial
import os

logger_level = 2
run_dig = False
use_reals = False
use_random_seed = False
gen_tcs = False
tmpdir = Path().home()/'tmp'
timeout =  5 * 1000
max_nonterm_refinement_depth = 3
n_inps = 100
invars = ""

SRC_DIR = Path(__file__).parent

DYNAMLTL_DIR = Path(__file__).parent.parent.parent
DIG_PYTHON = Path().home()/'miniconda3/bin/python3'

 
class CIL:
    PTR_VARS_PREFIX = 'PTR_'

    CIL_TRANSFORM_DIR = DYNAMLTL_DIR / "deps" / "sourceInstr"
    assert CIL_TRANSFORM_DIR.is_dir(), CIL_TRANSFORM_DIR

    CIL_EXE = CIL_TRANSFORM_DIR / "encoding.native"
    CIL_OPTS = "--save-temps -D HAPPY_MOOD" # --gcc=/usr/bin/gcc-5
    # CIL_CMD = partial("{cil_exe} {cil_opts} {ext} {inf} --out={outf} {opts}".format,
    #                   cil_exe=CIL_EXE, cil_opts=CIL_OPTS)
    CIL_CMD = partial("{cil_exe} {inf} {opts}".format, cil_exe=CIL_EXE)

    TRANSFORM_OPTS = partial("--inv={invar}".format)
    # TRANSFORM = lambda invar, inf, outf: CIL.CIL_CMD(ext="--dotransform", 
    #         inf=inf, outf=outf, opts=(CIL.TRANSFORM_OPTS(invar=invar)))
    TRANSFORM = lambda invar, inf: CIL.CIL_CMD(inf=inf, opts=(CIL.TRANSFORM_OPTS(invar=invar)))

    RANK_VALIDATE_OPTS = partial("--pos={pos} --ranks={ranks}".format)
    RANK_VALIDATE = lambda pos, ranks, inf, outf: CIL.CIL_CMD(ext="--dovalidate", 
            inf=inf, outf=outf, opts=(CIL.RANK_VALIDATE_OPTS(pos=pos, ranks=('"' + ranks + '"'))))


class CTRACE:
    SE_MIN_DEPTH = 20

    GCC_CMD = "gcc"
    # CIL_INSTRUMENT_DIR = SRC_DIR / "ocaml"
    # assert CIL_INSTRUMENT_DIR.is_dir(), CIL_INSTRUMENT_DIR

    COMPILE = "{gcc} {filename} -o {tmpfile}"
    COMPILE = partial(COMPILE.format, gcc=GCC_CMD)
    C_RUN = "./{exe} > {tracefile}"
    C_RUN = partial(C_RUN.format)
    

class DYNAMIC:
    CMD =DIG_PYTHON/'python3'
      
 
# class REACHABILITY:
#     TOOLS_HOME = Path(os.path.expandvars("$DYNAMITE_DEPS"))
#     ARCH = 64
#     SPEC = TOOLS_HOME / 'reachability.prp'
#     assert SPEC.is_file(), SPEC

# class CPAchecker:
#     CPA_HOME = Path(os.path.expandvars("$CPA_HOME"))
#     CPA_EXE = CPA_HOME / 'scripts' / 'cpa.sh'
    
#     CPA_COMMON_OPTS = "-spec {spec}".format(spec=REACHABILITY.SPEC) # -setprop cpa.predicate.encodeBitvectorAs=INTEGER
#     CPA_REACH_OPTS = "-predicateAnalysis -setprop counterexample.export.compressWitness=false"
#     CPA_VALIDATE_OPTS = partial("-witnessValidation -witness {witness}".format)
    
#     CPA_CMD = partial("{cpa_exe} {cpa_opts} {cpa_task_opts} {input}".format)
#     CPA_RUN = partial(CPA_CMD, cpa_exe=CPA_EXE, cpa_opts=CPA_COMMON_OPTS)

#     CPA_SHORT_NAME = 'cpa'
#     CPA_OUTPUT_DIR = 'output'
#     CPA_CEX_NAME = CPA_OUTPUT_DIR + '/' + 'Counterexample.1.assignment.txt'
#     CPA_CEX_SMTLIB_NAME = CPA_OUTPUT_DIR + '/' + 'Counterexample.1.smt2'
#     CPA_WITNESS_NAME = CPA_OUTPUT_DIR + '/' + 'Counterexample.1.graphml'
#     CPA_RES_KEYWORD = 'Verification result:'
      
# class Ultimate:
#     ULT_HOME = Path(os.path.expandvars("$ULT_HOME"))
#     ULT_EXE = lambda variant: Ultimate.ULT_HOME / 'releaseScripts' / 'default' / ('{variant}-linux'.format(variant=variant)) / 'Ultimate.py'

#     ULT_COMMON_OPTS = "--spec {spec} --architecture {arch}bit".format(spec=REACHABILITY.SPEC, arch=REACHABILITY.ARCH)
#     ULT_REACH_OPTS = partial("--witness-dir {witness_dir} --witness-name {witness_name}".format)
#     ULT_VALIDATE_OPTS = partial("--validate {witness_dir}/{witness_name}".format)

#     ULT_REACH_TASK = 'REACH'
#     ULT_VALIDATE_TASK = 'VALIDATE'

#     ULT_CMD = partial("{ult_exe} {ult_opts} {ult_task_opts} --file {input}".format)
#     ULT_RUN = lambda task, variant, witness_dir, witness_name, input: Ultimate.ULT_CMD(
#                     ult_exe=Ultimate.ULT_EXE(variant=variant), 
#                     ult_opts=Ultimate.ULT_COMMON_OPTS,
#                     ult_task_opts=(Ultimate.ULT_REACH_OPTS(witness_dir=witness_dir, witness_name=witness_name) if task is Ultimate.ULT_REACH_TASK
#                                     else Ultimate.ULT_VALIDATE_OPTS(witness_dir=witness_dir, witness_name=witness_name)), 
#                     input=input)

#     UAUTOMIZER_SHORT_NAME = 'uatm'
#     UAUTOMIZER_FULL_NAME = 'UAutomizer'

#     UTAIPAN_SHORT_NAME = 'utp'
#     UTAIPAN_FULL_NAME = 'UTaipan'
    
#     ULT_OUTPUT_DIR = ''
#     ULT_CEX_NAME = 'UltimateCounterExample.errorpath'
#     ULT_WITNESS_NAME = 'witness.graphml'
#     ULT_RES_KEYWORD = 'Result:'

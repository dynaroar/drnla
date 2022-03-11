import tempfile
import os
import subprocess, shlex
from enum import Enum
from pathlib import Path

from utils import settings, common


mlog = common.getLogger(__name__, settings.LoggerLevel)

class Setup(object):
    def __init__(self, inp):
        self.inp = inp
        self.source_path = self.inp.split(".")
        self.src_instr = self.source_path[0] + "_instr.c"
        self.src_validate = self.source_path[0] + "_validate.c"
        self.is_c_inp = inp.endswith(".c")
        self.tmpdir = Path(tempfile.mkdtemp(dir=settings.Tmpdir, prefix="dltl_"))
        self.invarsf = str(self.tmpdir / os.path.basename(self.inp)) + ".inv"
        self.invars_processed = (self.invarsf.split("."))[0] + "_refine.inv"
        self.vtracef = str(self.tmpdir / os.path.basename(self.inp)) + ".csv"
        self.vtrace_processed = (self.invarsf.split("."))[0] + "_refine.csv"
        self.symstates = None
        assert (self.is_c_inp), "\n Please input a C program: "+ inp
         
class CTransform(object):
    def __init__(self, config):
        self.source = config.inp
        self.instr = config.src_instr
        self.validate = config.src_validate
        
    def dtrans(self):
        dtrans_cmd = settings.Cil.dtrans(self.source)
        mlog.info(f'run CIL instrument for dynamic analysis:\n {dtrans_cmd} \n')
        # mlog.info(f'{self.source} transformed to:\n {self.instr}\n')
        # common.runCmd(dtrans_cmd)
        cp = subprocess.run(shlex.split(dtrans_cmd), capture_output=True, text=True)
        nla = cp.stdout.splitlines
        print(f'------output:\n {nla}')
  
    def strans(self, invars):
        strans_cmd = settings.Cil.strans(self.source, invars)
        mlog.info(f'run CIL instrument for static analysis:\n {strans_cmd} \n')
        # mlog.info(f'{self.source} transformed to:\n {self.validate}\n')
        subprocess.run(shlex.split(strans_cmd))
 
        
class DynamicAnalysis(object):
    def __init__(self, config):
        self.source = config.src_instr
        self.invarsf = config.invarsf
        self.vtracef = config.vtracef
        self.vtrace_processed = config.vtrace_processed
    def runTrace(self):
        vtrace_cmd = settings.Dynamic.vtrace_run(self.vtrace_processed, self.invarsf)
        mlog.info(f'run DIG dynamic on vtrace file:\n {vtrace_cmd}')
        # runCmd(vtrace_cmd)
    def runSource(self):
        source_cmd = settings.Dynamic.source_run(self.source, self.invarsf, self.vtracef)
        mlog.info(f'run DIG dynamic with source file:\n {source_cmd}')
        subprocess.run(shlex.split(source_cmd))

class StaticResult(Enum):
    UNSOUND = 1
    CORRECT = 2
    INCORRECT = 3
    UNKNOWN = 4
        
class StaticAnalysis(object):
    def __init__(self, config):
        self.source = config.src_validate
    def run(self):
        static_cmd = settings.Static.run(self.source)
        mlog.info(f'run Ultimate static analysis with command:\n {static_cmd}')
        subprocess.run(shlex.split(static_cmd))
        # sa_out, sa_err = common.runCmd(static_cmd)
        # print(f'------output:\n {sa_out}')
    
class OUAnalysis(object):
    def __init__(self, config):
        self.result = StaticResult.UNSOUND
        self.config = config

    def refine(self, iter, result):
        print(f"-------Refinement iteration {iter}------\n")
        cil_instr = CTransform(self.config)
        dynamic = DynamicAnalysis(self.config)
        if iter == 1:
            cil_instr.dtrans()
            dynamic.runSource()
        else:
            dynamic.runTrace()
        common.processInvars(self.config.invarsf, self.config.invars_processed)
        cil_instr.strans(self.config.invars_processed)
        static = StaticAnalysis(self.config)
        static.run()
        return result  
     
    def run(self):        
        iter= 1        
        while iter <= settings.RefineBound and self.result == StaticResult.UNSOUND:
            self.result = self.refine(iter, self.result)
            iter += 1
        return self.result
    

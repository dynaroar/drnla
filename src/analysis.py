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
        
    def dtrans(self, nla_ou):
        dtrans_cmd = settings.Cil.dtrans(self.source)
        mlog.info(f'------run CIL instrument for dynamic analysis:------')
        print(dtrans_cmd)
        outp = common.runCmd(dtrans_cmd)
        print(outp)
        nla_info = outp.splitlines()[1]
        nla = (nla_info.split(':')[1]).split(',')
        nla_ou[nla[0].strip()]=(nla[1].strip(), '', '')
        
        mlog.info(f'------nla expression output:\n {nla_ou}')
  
    def strans(self, invars):
        strans_cmd = settings.Cil.strans(self.source, invars)
        mlog.info(f'------run CIL instrument for static analysis:------')
        common.runCmd(strans_cmd)
  
class DynamicAnalysis(object):
    def __init__(self, config):
        self.source = config.src_instr
        self.invarsf = config.invarsf
        self.vtracef = config.vtracef
        self.vtrace_processed = config.vtrace_processed
    def runTrace(self):
        vtrace_cmd = settings.Dynamic.vtrace_run(self.vtrace_processed, self.invarsf)
        mlog.info(f'------run DIG dynamic on vtrace file:------')
        common.runCmd(vtrace_cmd)
    def runSource(self):
        source_cmd = settings.Dynamic.source_run(self.source, self.invarsf, self.vtracef)
        mlog.info(f'------run DIG dynamic with source file:-------')
        common.runCmd(source_cmd)
  
class StaticResult(Enum):
    UNSOUND = 1
    CORRECT = 2
    INCORRECT = 3
    UNKNOWN = 4
        
class StaticAnalysis(object):
    def __init__(self, config):
        self.source = config.src_validate
    def run(self, result):
        static_cmd = settings.Static.run(self.source)
        mlog.info(f'------run Ultimate static analysis:------')
        outp = common.runCmd(static_cmd)
        result_str = ""
        for line in outp.splitlines():
            if "RESULT:" in line:
                result_str = line
                mlog.info(f'------static analysis result (counterexample process):-------\n {line}')
        if "incorrect" in result_str:
            cex = common.getCex(outp.splitlines())
            print(f'counterexample: \n {cex}') 
            result = StaticResult.INCORRECT
            return result, cex
        elif "correct" in result_str:
            result = StaticResult.CORRECT
            return result, []
        else:
            cex = common.getCex(outp.splitlines())
            print(f'unable to prove counterexample: \n {cex}') 
            result = StaticResult.UNKNOWN
            return result, []
 
    
class OUAnalysis(object):
    def __init__(self, config):
        self.result = StaticResult.UNSOUND
        self.config = config
        self.nla_ou = {}

    def refine(self, iter, result, nla_ou):
        print(f"-------Refinement iteration {iter}------\n")
        cil_instr = CTransform(self.config)
        dynamic = DynamicAnalysis(self.config)
        if iter == 1:
            cil_instr.dtrans(nla_ou)
            dynamic.runSource()
        else:
            dynamic.runTrace()
        common.processInvars(self.config.invarsf, self.config.invars_processed, nla_ou)
        cil_instr.strans(self.config.invars_processed)
        static = StaticAnalysis(self.config)
        result, cex = static.run(result)
        return result  
     
    def run(self):        
        iter= 1        
        while iter <= settings.RefineBound and self.result == StaticResult.UNSOUND:
            self.result = self.refine(iter, self.result, self.nla_ou)
            iter += 1
        # return self.result, self.nla_ou
    

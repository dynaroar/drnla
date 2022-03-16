import tempfile
import os, re
import subprocess, shlex
from enum import Enum
from pathlib import Path

from utils import settings, common


mlog = common.getLogger(__name__, settings.LoggerLevel)

class StaticResult(Enum):
    CORRECT = 1
    INCORRECT = 2
    UNKNOWN = 3
class Result(Enum):
    CORRECT = 1
    INCORRECT = 2
    UNKNOWN = 3
    UNSOUND = 4

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
  
    
class StaticAnalysis(object):
    def __init__(self, config):
        self.source = config.src_validate

    def getCex(self, outp):
        cex=[]
        for i in range(len(outp)):
            line=outp[i]
            model_line = re.search(r'\[L(\d+)\].*COND\s(\w+)\s+(.*)', line)
            model_error = re.search('^\[L(\d+)\].*reach_error\(\)$', line)
            if model_line:
                line_info={}
                location, condition, expression = model_line.groups()
                mlog.info(f'loc:{location}, cond:{condition}, expr:{expression}')
                line_info['loc'] = location
                line_info['cond'] = condition
                line_info['exp'] = expression
                mregex = r'(\w+)=(-?\d+)'
                model_val = re.findall(mregex, outp[i+1])
                line_info['val'] = model_val
                cex.append(line_info)
            if model_error:
                line_err={}
                location = model_error.groups()
                line_err['loc'] = location
                line_err['exp'] = 'reach_error()' 
                mregex = r'(\w+)=(-?\d+)'
                model_val = re.findall(mregex, outp[i+1])
                line_err['val'] = model_val
                cex.append(line_err)
        return cex

    def runStatic(self, result):
        static_cmd = settings.Static.run(self.source)
        mlog.info(f'------run Ultimate static analysis:------')
        outp = common.runCmd(static_cmd)
        result_str = ""
        for line in outp.splitlines():
            if "RESULT:" in line:
                result_str = line
                mlog.info(f'------static analysis result (counterexample process):-------\n {line}')
        if "incorrect" in result_str:
            mlog.info(f'{outp}')
            cex = self.getCex(outp.splitlines())
            print(f'counterexample: \n {cex}') 
            result = StaticResult.INCORRECT
            return result, cex
        elif "correct" in result_str:
            result = StaticResult.CORRECT
            return result, []
        else:
            mlog.info(f'{outp}')
            cex = self.getCex(outp.splitlines())
            print(f'unable to prove counterexample: \n {cex}') 
            result = StaticResult.UNKNOWN
            return result, []
 
    
class OUAnalysis(object):
    def __init__(self, config):
        self.result = Result.UNSOUND
        self.config = config
        self.nla_ou = {}

    def dyGen(self, cex):
        pass
        
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
        sresult, cex = static.runStatic(result)
        if sresult == StaticResult.INCORRECT:
            return Result.UNSOUND
        elif sresult == StaticResult.CORRECT:
            return Result.SOUND
        else:
            return Result.UNKNOWN
      
    def run(self):        
        iter= 1        
        while iter <= settings.RefineBound and self.result == Result.UNSOUND:
            self.result = self.refine(iter, self.result, self.nla_ou)
            iter += 1
        # return self.result, self.nla_ou
    

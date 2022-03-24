import tempfile
import os, re, ast
import subprocess, shlex
from enum import Enum
from pathlib import Path

from transform import CTransform
from dynamic import DynamicAnalysis
from static import StaticAnalysis, StaticResult
from utils import settings, common
from utils.cparser import *
from solver import *


mlog = common.getLogger(__name__, settings.LoggerLevel)

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
        self.vtrace_genf = (self.invarsf.split("."))[0] + "_gen.csv"
        self.symstates = None
        assert (self.is_c_inp), "\n Please input a C program: "+ inp         
    
    
class OUAnalysis(object):

    def __init__(self, config):
        self.result = Result.UNSOUND
        self.config = config
        self.nla_ou = {}
        self.if_small = 'if_too_small'
        self.if_big = 'if_too_big'
        self.else_small = 'else_too_small'
        self.else_big = 'else_too_big'

    def getReach(self, vars_list):
        error_case = ''
        for var in vars_list:
            if self.if_small in var:
                error_case = var
            if self.if_big in var:
                error_case = var
            if self.else_small in var:
                error_case = var
            if self.else_big in var:
                error_case = var
        return error_case
         
 
    def dynGen(self, cex_z3, error_case):
        mlog.debug(f'more model for formula:\n {cex_z3}')
        dsolver = DynSolver(cex_z3)
        models = dsolver.gen_model()
        dsolver.write_vtrace(error_case, self.config.vtrace_genf)
        gen_dynamic = DynamicAnalysis(self.config)
        gen_dynamic.runTrace(self.config.vtrace_genf)
 
        pass
     
    def refine(self, iter, result, nla_ou):
        mlog.info(f"-------Refinement iteration {iter}------\n")
        cil_instr = CTransform(self.config)
        dynamic = DynamicAnalysis(self.config)
        if iter == 1:
            cil_instr.dtrans(nla_ou)
            dynamic.runSource()
            invar_list = common.processInvars(self.config.invarsf)
            mlog.debug(f'------processed invars from dig: \n{invar_list}')
            common.initInvars(self.config.invars_processed, invar_list, nla_ou)
        else:
            dynamic.runTrace()


        cil_instr.strans(self.config.invars_processed)
        static = StaticAnalysis(self.config)
        sresult, cex = static.runStatic(result)
        if sresult == StaticResult.INCORRECT:
            mlog.debug(f'------counterexample from static analysis: \n {cex}\n')
                
            cex_parser = UltCexParser()
            cex_z3 = cex_parser.to_z3(cex)
            cex_vars = [*cex_parser.sym_tab]
            mlog.debug(f'symbols from cex formula:\n{cex_vars}')
            error_case = self.getReach(cex_vars) 
            mlog.debug(f'error case: \n {error_case}')
            self.dynGen(cex_z3, error_case)
            
            if self.else_big in error_case:
                mlog.debug(f'----strengthen C2 on iteration {iter}------\n')
            elif self.if_small in error_case:
                mlog.debug(f'----widen C1 on iteration {iter}------\n')
            elif self.if_big in error_case:
                mlog.debug(f'----strengthen C1 on iteration {iter}------\n')
            elif self.else_small in error_case:
                mlog.debug(f'----widen C2 on iteration {iter}------\n')
            else:
                raise ValueError(f'Reach error case unable to handle: {error_case}')
     
            return Result.UNSOUND
        elif sresult == StaticResult.CORRECT:
            return Result.CORRECT
        else:
            return Result.UNKNOWN
      
    def run(self):        
        iter= 1        
        while iter <= settings.RefineBound and self.result == Result.UNSOUND:
            self.result = self.refine(iter, self.result, self.nla_ou)
            iter += 1
        # return self.result, self.nla_ou
    

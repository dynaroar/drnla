import tempfile
import os, re, ast
import subprocess, shlex
from enum import Enum
from pathlib import Path

from transform import CTransform
from dynamic import DynamicAnalysis
from static import StaticAnalysis, StaticResult
from utils import settings, common
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
        self.is_c_inp = inp.endswith(".c")
        assert (self.is_c_inp), "\n Please input a C program: "+ inp         

        self.source_path = self.inp.split(".")
        self.src_instr = self.source_path[0] + "_instr.c"
        self.src_validate = self.source_path[0] + "_validate.c"
        self.tmpdir = Path(tempfile.mkdtemp(dir=settings.Tmpdir, prefix="dltl_"))
        self.invarsf = str(self.tmpdir / os.path.basename(self.inp)) + ".inv"
        self.invars_refine = (self.invarsf.split("."))[0] + "_refine.inv"
        self.vtracef = str(self.tmpdir / os.path.basename(self.inp)) + ".csv"
        self.vtrace_genf = (self.invarsf.split("."))[0] + "_gen.csv"
        self.symstates = None

    
    
class OUAnalysis(object):

    def __init__(self, config):
        self.config = config
        self.cil_trans = CTransform(config)
        self.dynamic = DynamicAnalysis(config)
        self.static = StaticAnalysis(config)
        
        self.result = Result.UNSOUND
        self.nla_ou = {}
        self.if_small = 'if_too_small'
        self.if_big = 'if_too_big'
        self.else_small = 'else_too_small'
        self.else_big = 'else_too_big'

    def get_reach(self, vars_list):
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
         
 
    def dyn_gen(self, cex_str):
        dsolver = DynSolver(cex_str)
        dsolver.parse_to_z3()
        error_case = self.get_reach(dsolver.cex_vars) 
        mlog.debug(f'more model for formula:\n {dsolver.formula}')
        # models = dsolver.gen_model()
        dsolver.init_vtrace(error_case, self.config.vtrace_genf)
        iter = 0
        gen_cex = dsolver.get_cex_text()
        cex_formula = dsolver.formula
        pre = '(1 != 0)'
        while iter <= 8 and (not gen_cex == ''):
            dsolver.update_cex(gen_cex)
            dsolver.parse_to_z3()
            pre = pre.strip('"')
            pre_z3 = dsolver.parse(pre)
            gen_z3f = And(pre_z3, dsolver.formula)
            dsolver.update_formula(gen_z3f)
            mlog.debug(f'------find models of: pre /\ cex_z3:\n {gen_z3f}')
            dsolver.gen_model()
            dsolver.update_vtrace()
            self.dynamic.run_trace(self.config.vtrace_genf)
            [(gen_case, gen_invars)] = self.dynamic.get_invars()
            mlog.debug(f'------invars from cex generalized (dig):\n {gen_case}; {gen_invars}')
            pre_learn = ' && '.join(gen_invars)
            pre = f'\"{pre} && !({pre_learn})\"'
            mlog.debug(f'------conjunction of all previous invars predicate:\n {pre}')
            self.cil_trans.vtrans(pre, f'\"{gen_case}\"')
            gen_result, gen_cex = self.static.run_static()
            mlog.debug(f'------static result for predicate: {gen_result} \n {gen_cex}')
            
            iter += 1
        return dsolver.vtrace_genf
     
    def refine(self, iter, result, nla_ou):
        mlog.info(f"-------Refinement iteration {iter}------\n")
        if iter == 1:
            self.cil_trans.dtrans(nla_ou)
            self.dynamic.run_source()
            invar_list = self.dynamic.get_invars()
            mlog.debug(f'------invars from dig (initial refinement): \n{invar_list}')
            self.dynamic.init_invars(invar_list, nla_ou)
 
        self.cil_trans.strans()
        sresult, cex_str = self.static.run_static()
        if sresult == StaticResult.INCORRECT:
            mlog.debug(f'------counterexample from static analysis: \n {cex_str}\n')
                
            rsolver = DynSolver(cex_str)
            rsolver.parse_to_z3()
            mlog.debug(f'symbols from cex formula:\n{rsolver.cex_vars}')
            error_case = self.get_reach(rsolver.cex_vars) 
            mlog.debug(f'error case: \n {error_case}')
            genf = self.dyn_gen(cex_str)
            
            if self.else_big in error_case:
                mlog.debug(f'----strengthen C2 on iteration {iter}------\n')
                # self.dynamic.join_vtrace(error_case)
                self.dynamic.run_trace(self.config.vtrace_genf)
                [(ref_case, ref_invars)] = self.dynamic.get_invars()
                # select conjunction? ....
                gen_invars = ' && '.join(ref_invars)
                ref_invars = f'!({gen_invars})'
                mlog.debug(f'------ negated invars from generalized cex trace (refine):\n {ref_case}: {ref_invars}')
                self.dynamic.conj_ou(ref_case, ref_invars, nla_ou)      
                
                
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
    

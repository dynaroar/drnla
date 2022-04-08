from enum import Enum

from dsetup import *
from transform import CTransform
from dynamic import DynamicAnalysis
from static import StaticAnalysis, StaticResult
from solver import *


mlog = common.getLogger(__name__, settings.logger_level)


cex_test = r"""
[L355]              int x ;
[L356]              int y ;
[L357]              int if_too_small_3 ;
[L358]              int else_too_big_3 ;
[L359]              int else_too_small_3 ;
[L360]              int if_too_big_3 ;
[L363]  COND FALSE  !(x * y < 0)
        VAL         [x=0, y=0]
[L375]              if_too_big_3 = 1
        VAL         [if_too_big_3=1, x=0, y=0]
[L376]              reach_error()
        VAL         [if_too_big_3=1, x=0, y=0]
 """


class Result(Enum):
    CORRECT = 1
    INCORRECT = 2
    UNKNOWN = 3
    UNSOUND = 4
     
class OUAnalysis(object):

    def __init__(self, config):
        
        self.config = config
        self.init_tools()
         
        self.result = Result.UNSOUND
        self.nla_ou = {}
        self.if_small = 'if_too_small'
        self.if_big = 'if_too_big'
        self.else_small = 'else_too_small'
        self.else_big = 'else_too_big'

    def init_tools(self):
      self.cil_trans = CTransform(self.config) 
      self.dynamic = DynamicAnalysis(self.config)
      self.static = StaticAnalysis(self.config)
          
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
         
# old dyn_gen: 
    # def dyn_gen(self, cex_str):
    #     dsolver = DynSolver(cex_str)
    #     dsolver.parse_to_z3()
    #     error_case = self.get_reach(dsolver.cex_vars) 
    #     mlog.debug(f'more model for formula:\n {dsolver.formula}')
    #     # models = dsolver.gen_model()
    #     dsolver.init_cvars(error_case)
    #     dsolver.init_vtrace(error_case, self.config.vtrace_genf)
    #     iter = 0
    #     gen_cex = dsolver.get_cex_text()
    #     cex_formula = dsolver.formula
    #     pre = '(1 != 0)'
    #     while iter <= 5 and (not gen_cex == ''):
    #         dsolver.init_vtrace(error_case, self.config.vtrace_cexf)
    #         dsolver.update_cex(gen_cex)
    #         dsolver.parse_to_z3()
    #         pre = pre.strip('"')
    #         pre_z3 = dsolver.parse(pre)
    #         gen_z3f = And(pre_z3, dsolver.formula)
    #         dsolver.update_formula(gen_z3f)
    #         mlog.debug(f'------find models of (iter {iter}): pre /\ cex_z3:\n {gen_z3f}')
    #         dsolver.gen_model()
    #         dsolver.update_vtrace_gen(self.config.vtrace_genf)
    #         dsolver.update_vtrace_pre(self.config.vtrace_cexf)
    #         self.dynamic.run_trace(self.config.vtrace_cexf)
    #         # self.dynamic.run_trace(self.config.vtrace_genf)
    #         [(gen_case, gen_invars)] = self.dynamic.get_invars()
    #         mlog.debug(f'------invars from cex generalized (dig):\n {error_case}; {gen_invars}')
    #         pre_learn = ' && '.join(gen_invars)
    #         pre = f'\"{pre} && !({pre_learn})\"'
    #         mlog.debug(f'------conjunction of all previous invars predicate:\n {pre}')
    #         self.cil_trans.vtrans(pre, f'\"{error_case}\"')
    #         gen_result, gen_cex = self.static.run_static()
    #         # mlog.debug(f'------static result for predicate: {gen_result} \n {gen_cex}')
    #         iter += 1

    def dyn_gen(self, cex_str):
        dsolver = DynSolver(cex_str)
        # dsolver = DynSolver(cex_test)
        dsolver.parse_to_z3()
        mconstr = True
       
        error_case = self.get_reach(dsolver.cex_vars) 
        # mlog.debug(f'more model for formula:\n {dsolver.formula}')
        dsolver.init_cvars(error_case)
        
        dsolver.init_vtrace(error_case, self.config.vtrace_cexf)
        dsolver.gen_model(mconstr)
        dsolver.write_vtrace_error(self.config.vtrace_cexf)
        self.config.vtrace_cexf = '/home/cyrus/dynamic-ltl/dynamiteLTL/test-tmp/ex3/traces.tcs'
        self.dynamic.run_trace(self.config.vtrace_cexf)

        for i in range(20):
            print(dsolver.models[i])
        
        invars_i_str = self.dynamic.get_invars()
        if invars_i_str:
            [(cex_case, cex_invars_str)] = invars_i_str
        else:
            raise ValueError(f'empty invars from dynamic: {invars_str}')
            
        invars_i = list(map(lambda inv_str: dsolver.parse(inv_str), cex_invars_str))
        mlog.debug(f'invars from cex-gen snaps (initial cex): \n {invars_i}')

        for ci in invars_i:
            # mlog.debug(f'Inv from cex-gen snaps: \n {inv}') # 
            mconstr = dsolver.error_zid(Not(ci))
            
            dsolver.init_vtrace(error_case, self.config.vtrace_negf)
            dsolver.gen_model(mconstr)
            # mlog.debug(f'models: \n {dsolver.models}')
            dsolver.write_vtrace_error(self.config.vtrace_negf)
            self.dynamic.join_vtrace(self.config.vtrace_cexf, self.config.vtrace_negf, self.config.vtrace_joinf)
            self.dynamic.run_trace(self.config.vtrace_joinf)
            invars_j_str = self.dynamic.get_invars()
            if invars_j_str:
                [(join_case, join_invars_str)] = invars_j_str
                invars_j = list(map(lambda inv_str: dsolver.parse(inv_str), join_invars_str))
                mlog.debug(f'invars from the joined traces.\n {invars_j}')
                

                
                pass
           
            
    def refine(self, iter, result, nla_ou):
        mlog.info(f"\n-------Refinement iteration {iter}------\n")
        if iter == 1:
            self.cil_trans.dtrans(nla_ou)
            if settings.init_ou:
                invar_list = []
                for loc, value in nla_ou.items():
                    (_, if_ou, else_ou) = value
                    init_invar = [(f'vtrace_if_{loc}', ['0 == 0']), (f'vtrace_else_{loc}', ['1 == 0'])]
                    invar_list = invar_list + init_invar
                self.dynamic.init_invars(invar_list, nla_ou)
                mlog.debug(f'------initial OU Mapping: \n{nla_ou}')
            else:
                self.dynamic.run_source()
                invar_list = self.dynamic.get_invars()
                mlog.debug(f'------invars from dig (initial refinement): \n{invar_list}')
                self.dynamic.init_invars(invar_list, nla_ou)
   
        self.config.update_basename(iter)
        self.init_tools()
    
        self.cil_trans.strans()
        sresult, cex_str = self.static.run_static()
        if sresult == StaticResult.INCORRECT:
            mlog.debug(f'------counterexample from static analysis (iteration {iter}): \n {cex_test}\n')
                
            # rsolver = DynSolver(cex_str)
            rsolver = DynSolver(cex_test)
            rsolver.parse_to_z3()
            mlog.debug(f'symbols from cex formula:\n{rsolver.cex_vars}')
            error_case = self.get_reach(rsolver.cex_vars) 
            mlog.debug(f'error case: \n {error_case}')

            self.dyn_gen(cex_str)
            self.dynamic.run_trace(self.config.vtrace_genf)
            [(ref_case, ref_invars)] = self.dynamic.get_invars()
          
            if self.else_big in error_case:
                mlog.debug(f'----strengthen ELSE on iteration {iter}------\n')
                # mlog.debug(f'------ invars from generalized cex trace (refine):\n {ref_case}: {ref_invars}')
                self.dynamic.conj_ou(ref_case, ref_invars, nla_ou)   
                 
            elif self.if_small in error_case:                
                mlog.debug(f'----widen IF on iteration {iter}------\n')
                # mlog.debug(f'------invars from generalized cex trace (refine):\n {ref_case}: {ref_invars}')
                self.dynamic.disj_ou(ref_case, ref_invars, nla_ou)
                 
            elif self.if_big in error_case:
                mlog.debug(f'----strengthen IF on iteration {iter}------\n')
                self.dynamic.conj_ou(ref_case, ref_invars, nla_ou)   
                
            elif self.else_small in error_case:
                mlog.debug(f'----widen ELSE on iteration {iter}------\n')
                self.dynamic.disj_ou(ref_case, ref_invars, nla_ou)
 
            else:
                raise ValueError(f'Reach error case unable to handle: {error_case}')
     
            return Result.UNSOUND
        elif sresult == StaticResult.CORRECT:
            return Result.CORRECT
        else:
            return Result.UNKNOWN
      
    def run(self):        
        iter= 1        
        while iter <= settings.refine and self.result == Result.UNSOUND:
            self.result = self.refine(iter, self.result, self.nla_ou)
            iter += 1
        # return self.result, self.nla_ou
    

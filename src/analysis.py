from enum import Enum

from dsetup import *
from transform import CTransform
from dynamic import DynamicAnalysis
from static import StaticAnalysis, StaticResult
from solver import *
from utils.smt import *


mlog = common.getLogger(__name__, settings.logger_level)
  
class Result(Enum):
    CORRECT = 1
    INCORRECT = 2
    UNKNOWN = 3
    UNSOUND = 4

     
class OUAnalysis(object):

    def __init__(self, config):
        
        self.config = config
        self.init_tools()
         
        self.ou_result = Result.UNSOUND
        self.nla_ou = {}
        self.if_small = 'if_too_small'
        self.if_big = 'if_too_big'
        self.else_small = 'else_too_small'
        self.else_big = 'else_too_big'
        self.verify_result = 'unknown'
        self.ou_type = '_approximate'
        self.ou_str = '_empty'
        self.ou_init_str = '_empty'
        self.refine_steps = ['init_random']
        
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
         
    def write_ou(self):
        '''write file and convert OU mapping to string
        '''
        fw = open(self.config.ou_mapf, 'w+')
        
        map_str = []
        for loc_str, ou_val in self.nla_ou.items():
            nla, if_ou, else_ou = ou_val
            nla_str = Z3.to_string(nla)
            if_ou_str = '&&'.join(list(map(lambda inv: Z3.to_string(inv),if_ou)))
            else_ou_str = '&&'.join(list(map(lambda inv: Z3.to_string(inv),else_ou)))
            fw.write(f'{loc_str};{if_ou_str}')
            map_str.append(f'MAP:{loc_str};{self.ou_type};{nla_str};{if_ou_str};{else_ou_str}')
        fw.close()
        return '\n'.join(map_str)
       
        
    def refine_cex(self, invars_i, dsolver):
        '''join more snaps to vtrace, strengthen the final result.
        '''
        for ci in invars_i:
            # mlog.debug(f'Inv from cex-gen snaps: \n {inv}') #
            mconstr = dsolver.error_zid(Not(ci))
            dsolver.init_vtrace(self.config.vtrace_negf)
            genj_result = dsolver.gen_model(mconstr)
            # mlog.debug(f'models: \n {dsolver.models}')
            if genj_result == 'sat':
                dsolver.write_vtrace_error(self.config.vtrace_negf)
                self.dynamic.join_vtrace(self.config.vtrace_cexf, self.config.vtrace_negf, self.config.vtrace_joinf)
                self.dynamic.run_trace(self.config.vtrace_joinf)
                invars_j_str = self.dynamic.get_invars()
            else:
                mlog.info(f'----cex X !c_i not sat exit to next one----')
                continue
            if invars_j_str:
                [(join_case, join_invars_str)] = invars_j_str
                invars_j = list(map(lambda inv_str: dsolver.parse(inv_str), join_invars_str))
                mlog.debug(f'invars_j from the joined traces.\n {invars_j}')
                invars_j = dsolver.rm_weak(dsolver.simp_eqs(invars_j))
                mlog.debug(f'weak invars_j removed from the joined traces.\n {invars_j}')
                for fi in invars_i:
                    for fj in invars_j:
                        mlog.debug(f'check the same template in: \n {fi} and {fj}')
                        compare = Z3.is_same_template(fi, fj)
                        if compare and (not dsolver.is_equal(fi, fj)):
                            template, c1, c2 = compare
                            mlog.debug(f'found same template in {fi} and {fj}: \n {template, c1, c2}')
                            def get_invarsk(ck):
                                mconstr = dsolver.error_zid(Not (Z3.expr_of_terms(template) <= ck))
                                dsolver.init_vtrace(self.config.vtrace_uppf)
                                genk_result = dsolver.gen_model(mconstr)
                                assert genk_result == 'sat', f'unsat result in upper ck:\n {mconstr}'
                                dsolver.write_vtrace_error(self.config.vtrace_uppf)
                                self.dynamic.join_vtrace(self.config.vtrace_cexf, self.config.vtrace_uppf, self.config.vtrace_joinf)
                                self.dynamic.run_trace(self.config.vtrace_joinf)
                                invars_k_str = self.dynamic.get_invars()

                                assert invars_k_str, f'diverge model generated for C_k join, {mconstr}'
                                [(join_case, join_invars_str)] = invars_k_str
                                return list(map(lambda inv_str: dsolver.parse(inv_str), join_invars_str))

                            def remove_loop(ck):
                                r = 1
                                while r<= settings.repeat:
                                    r += 1
                                    '''check if fi and fj removed from resulted invars.
                                    '''
                                    invars_k = get_invarsk(ck)
                                    mlog.info(f'invars_k: {invars_k}')
                                    if dsolver.not_in(fi, invars_k) and dsolver.not_in(fj, invars_k):
                                        mlog.info(f'inva removed: {fi} and {fj}')
                                        self.dynamic.add_vtrace(self.config.vtrace_negf, self.config.vtrace_genf)
                                        self.dynamic.add_vtrace(self.config.vtrace_uppf, self.config.vtrace_genf)
                                        break
                                    else:
                                        if ck > 0:
                                            ck += 2
                                        elif ck == 0:
                                            break
                                        else:
                                            ck = settings.upper
                            if 0<c1 and c1<c2:
                                ck = settings.upper
                                remove_loop(ck)
                                if c1>c2 and c2>0:
                                    ck = 0
                                    remove_loop(ck)
                            if c1<c2 and c2<0:
                                ck = 0
                                remove_loop(ck)
                            if 0>c1 and c1>c2:
                                ck = -settings.upper
                                remove_loop(ck)
                        else:
                            continue

                        
    def dyn_gen(self, cex_str):
        dsolver = DynSolver(cex_str)
        # dsolver = DynSolver(cex_test)
        dsolver.parse_to_z3()
        mconstr = True
        geni_result = dsolver.gen_model(True)
        assert geni_result == 'sat', f'------unsat for initial cex snaps: \n {cex_str}'
        error_case = self.get_reach(dsolver.cex_vars)
        dsolver.init_cvars(error_case)
        dsolver.init_vtrace(self.config.vtrace_cexf)
        dsolver.init_vtrace(self.config.vtrace_genf)
        dsolver.write_vtrace_error(self.config.vtrace_cexf)
        dsolver.write_vtrace_error(self.config.vtrace_genf)

        self.dynamic.run_trace(self.config.vtrace_cexf)
        
        invars_i_str = self.dynamic.get_invars()
        if invars_i_str:
            [(cex_case, cex_invars_str)] = invars_i_str
            self.dynamic.ref_case = cex_case
        else:
            raise ValueError(f'empty invars from dynamic(i): {invars_i_str}')
            
        invars_i = list(map(lambda inv_str: dsolver.parse(inv_str), cex_invars_str))
        mlog.debug(f'invars from cex-gen snaps (initial cex): \n {invars_i}')

        loc_case = re.findall(r'\d+', cex_case)[0]
        (nla, if_ou, else_ou) = self.nla_ou[loc_case]
        if 'if' in cex_case:
            origin_ou = if_ou
        else:
            origin_ou = else_ou
        mlog.debug(f'origin ou: {origin_ou}')

        if 'small' in error_case:
            ou_core, cex_core = dsolver.unsatcore_ou(origin_ou,invars_i)
            mlog.debug(f'unsat core for {cex_case} and {error_case}: \n {ou_core} -> {cex_core}')
        else:
            cex_core = None

        if cex_core:
            invars_i = cex_core
            mlog.debug(f'new C_i: {invars_i}')
            # self.refine_cex(invars_i, dsolver)
            return invars_i
        else:
            # invars_i = dsolver.rm_weak(dsolver.simp_eqs(invars_i))
            mlog.debug(f'weak invars removed from cex-gen snaps (initial cex): \n {invars_i}')
            # self.refine_cex(invars_i, dsolver)
            # return True
            return invars_i
      
            
    def refine(self, iter, result, nla_ou):
        mlog.info(f"\n-------Refinement iteration {iter}------\n")
        if iter == 1:
            if settings.bv:
                nla_ou['16']=(DynSolver.parse('(a|b) == 0'), [],[])
            else:
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
            self.ou_init_str = self.write_ou()

        mlog.info(f'{iter}th mSOFAR({self.write_ou()})')
        self.config.update_basename(iter)
        self.init_tools()

        # for loc, (nla, if_ou, else_ou) in nla_ou.items():
        #     verdict_z3 = DynSolver.parse(settings.verdict)
        #     if DynSolver.is_equal(And(if_ou), verdict_z3) and DynSolver.is_equal(And(else_ou), Not(verdict_z3)):
        #         return Result.CORRECT
        
        self.cil_trans.strans()
        sresult, cex_str = self.static.run_reach(self.config.src_validate)

        if sresult == StaticResult.INCORRECT:
            mlog.debug(f'------counterexample from static analysis (iteration {iter}): \n {cex_str}\n')
                
            rsolver = DynSolver(cex_str)
            rsolver.parse_to_z3()
             
            mlog.debug(f'symbols from cex formula:\n{rsolver.cex_vars}')
            error_case = self.get_reach(rsolver.cex_vars)
            mlog.debug(f'error case: \n {error_case}')

            # gen_res = self.dyn_gen(cex_str)
            ref_invars = self.dyn_gen(cex_str)
            ref_case = self.dynamic.ref_case

            # if gen_res == True:
            #     self.dynamic.run_trace(self.config.vtrace_genf)
            #     invars_gen_str = self.dynamic.get_invars()
            #     assert invars_gen_str, f'empty invars from dyn_gen snaps: {invars_gen_str}'
            #     [(ref_case, ref_invars_str)] = invars_gen_str
            #     ref_invars = list(map(lambda inv: DynSolver.parse(inv), ref_invars_str))  
            #     mlog.debug(f'------invars(z3) from dyn_gen: \n {ref_invars}')
            # else:
            #     ref_case = self.dynamic.ref_case
            #     ref_invars = gen_res
                      
            if self.else_big in error_case:
                mlog.debug(f'----strengthen ELSE on iteration {iter}------\n')
                # self.dynamic.conj_ou(ref_case, ref_invars_str, nla_ou)   
                self.refine_steps.append(f'strengthen-else-iteration-{iter}')
                self.dynamic.conj_ou(ref_case, ref_invars, nla_ou)   
                 
            elif self.if_small in error_case:                
                mlog.debug(f'----widen IF on iteration {iter}------\n')
                self.refine_steps.append(f'widen-if-iteration-{iter}')
                self.dynamic.disj_ou(ref_case, ref_invars, nla_ou)
                 
            elif self.if_big in error_case:
                mlog.debug(f'----strengthen IF on iteration {iter}------\n')
                # self.dynamic.conj_ou(ref_case, ref_invars_str, nla_ou)   
                self.refine_steps.append(f'strengthen-if-iteration-{iter}')
                self.dynamic.conj_ou(ref_case, ref_invars, nla_ou)   
                
            elif self.else_small in error_case:
                mlog.debug(f'----widen ELSE on iteration {iter}------\n')
                self.refine_steps.append(f'widen-else-iteration-{iter}')
                self.dynamic.disj_ou(ref_case, ref_invars, nla_ou)
 
            else:
                raise ValueError(f'Reach error case is unable to handle: {error_case}')
     
            return Result.UNSOUND
        elif sresult == StaticResult.CORRECT:
            mlog.info(f'Static validation returns correct for OU mapping, exit refinement step..')
            return Result.CORRECT
        # elif (sresult == StaticResult.UNKNOWN) and (settings.verdict == '1==1'):
        #     return Result.CORRECT
        else:
            # for loc, (nla, if_ou, else_ou) in nla_ou.items():
            #     verdict_z3 = DynSolver.parse(settings.verdict)
            #     if DynSolver.is_equal(And(if_ou), verdict_z3):
            #         return Result.CORRECT
            #     else:
            return Result.UNKNOWN
      
    def nla_run(self):        
        iter= 1        
        while iter <= settings.refine and self.ou_result == Result.UNSOUND:
            self.ou_result = self.refine(iter, self.ou_result, self.nla_ou)
            mlog.info(f'------{iter}th refinement result: \n {self.nla_ou}')
            iter += 1

        if self.ou_result == Result.UNKNOWN and (settings.verdict != '1==1'):
            mlog.info(f'verdict check for unknown static result (final): ')
            for loc, (nla, if_ou, else_ou) in self.nla_ou.items():
                verdict_z3 = DynSolver.parse(settings.verdict)
                if DynSolver.is_equal(And(if_ou), verdict_z3) and DynSolver.is_equal(And(else_ou), Not(verdict_z3)):
                    self.ou_result = Result.CORRECT
            
        if self.ou_result == Result.CORRECT:
            self.ou_type = 'exact'
        else:
            self.ou_type = 'approximate'
        
        # return self.result, self.nla_ou
    def verify_run(self):
        '''transform to linear program first
        '''
        self.ou_str = self.write_ou()
        self.cil_trans.ltrans()
        result = self.verify_result
        if settings.prop == 'reach':
            sresult, cex_str = self.static.run_reach(self.config.linearf)
        if settings.prop == 'termination':
            sresult, cex_str = self.static.run_term()
        if settings.prop == 'ltl':
            sresult, cex_str = self.static.run_ltl()

        if sresult == StaticResult.CORRECT:
              self.verify_result = 'valid'
        if sresult == StaticResult.INCORRECT:
              self.verify_result = 'invalid'
        if sresult == StaticResult.UNKNOWN:
              self.verify_result = 'unkown'
               

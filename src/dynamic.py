import re, shutil
from utils import settings
from utils.smt import *

import utils.common as CM
from solver import *
from z3 import *

mlog = CM.getLogger(__name__, settings.logger_level)


class DynamicAnalysis(object):
    def __init__(self, config):
        self.source = config.src_instr
        self.invarsf = config.invarsf
        self.invars_refine = config.invars_refine
        self.vtracef = config.vtracef
        self.vtrace_genf = config.vtrace_genf
        self.vtrace_cexf = config.vtrace_cexf
        self.vtrace_joinf = config.vtrace_joinf

        
         
    def run_trace(self, trace_file):
        vtrace_cmd = settings.Dynamic.vtrace_run(trace_file, self.invarsf)
        # mlog.info(f'------run DIG dynamic on vtrace file:------') 
        CM.run_cmd(vtrace_cmd)
        
    def run_source(self):
        source_cmd = settings.Dynamic.source_run(self.source, self.invarsf, self.vtracef)
        # mlog.info(f'------run DIG dynamic with source file:-------')
        CM.run_cmd(source_cmd)

        
    def init_invars(self, invs_list, nla_ou):
        fw = open(self.invars_refine, 'w')
        for loc_str, invars in invs_list:
            if 'vtrace_if_' in loc_str:
                loc_if = re.findall(r'\d+', loc_str)[0]
                (nla, if_ou, else_ou) = nla_ou[loc_if]
                if_ou = [DynSolver.parse(inv) for inv in invars]
                nla_ou[loc_if] = (nla, if_ou, else_ou)
            if 'vtrace_else_' in loc_str:
                loc_else = re.findall(r'\d+', loc_str)[0]
                (nla, if_ou, else_ou) = nla_ou[loc_else]
                else_ou = [DynSolver.parse(inv) for inv in invars]
                nla_ou[loc_else] = (nla, if_ou, else_ou)

        ''' writing invars formula back to C string .inv file
        '''           
        for loc, (nla, if_ou, else_ou) in nla_ou.items():
            loc_if = 'vtrace_if_'+ loc
            loc_else = 'vtrace_else_'+ loc
            # if_ou, else_ou = list(set(if_ou).difference(else_ou)), list(set(else_ou).difference(if_ou))
            if_ou, else_ou = DynSolver.remove_identical(if_ou, else_ou)
            mlog.debug(f'removed equal formulae: \n if, {if_ou} \n else, {else_ou}')
            nla_ou[loc] = (nla, if_ou, else_ou)
            if_ou_str = list(map(lambda inv: Z3.to_string(inv), if_ou))
            else_ou_str = list(map(lambda inv: Z3.to_string(inv), else_ou))
            fw.writelines(loc_if+';'+' && '.join(if_ou_str)+'\n')
            fw.writelines(loc_else+';'+' && '.join(else_ou_str)+'\n')
        fw.close()            

 
        
    def get_invars(self):
        fr = open(self.invarsf, "r")
        invs_list = []
        for line in fr:
            # mlog.debug(f'------read invariant files (dig run): \n {line}')
            invars=[]
            iterms = re.split(";", line.rstrip('\n'))
            for inv in iterms[1:]:
                if inv[-1] == "1":
                    invars.append(inv[:-1].strip())
            invs_list.append((iterms[0].strip(),invars))
        fr.close()
        return invs_list

    def replace_invars(self, vtrace_name, vtrace_list):
        fr = open(self.invars_refine, 'r')
        static_invars = fr.readlines()
        fr.close()
        fw = open(self.invars_refine, 'w+')
    
        for line in static_invars:
            if vtrace_name in line:
                fw.writelines(vtrace_name + ';' + ' && '.join(vtrace_list)+'\n')
            else:
                fw.writelines(line)
        fw.close()
        
    def conj_ou(self, ref_case, ref_invars, nla_ou):
        """Update ou mapping for conjunction refinement.
        This will also update refine.inv file for static run. 
        """
        gen_invars = ' && '.join(ref_invars)
        ref_conj_str = f'!({gen_invars})'
        ref_conj = DynSolver.parse(ref_conj_str)
        [ref_loc] = re.findall(r'\d+', ref_case) 
        (nla, if_ou, else_ou) = nla_ou[ref_loc]
        if 'if' in ref_case:
            if_ou.append(ref_conj)
            vtrace_name = f'vtrace_if_{ref_loc}'
            # if_ou, else_ou = DynSolver().remove_identical(if_ou, else_ou)
            nla_ou[ref_loc] = (nla, if_ou, else_ou)
            if_ou_str = list(map(lambda inv: Z3.to_string(inv),if_ou))
            self.replace_invars(vtrace_name, if_ou_str)
        elif 'else' in ref_case:
            else_ou.append(ref_conj)
            vtrace_name = f'vtrace_else_{ref_loc}'
            # if_ou, else_ou = DynSolver().remove_identical(if_ou, else_ou)
            nla_ou[ref_loc] = (nla, if_ou, else_ou)
            else_ou_str = list(map(lambda inv: Z3.to_string(inv),else_ou))
            self.replace_invars(vtrace_name, else_ou_str)

        
    def disj_ou(self, ref_case, ref_invars_str, nla_ou):
        """Update ou mapping for disjunction refinement.
         This will also update refine.inv file for static run. 
        """

        ref_invars = list(map(lambda inv: DynSolver.parse(inv), ref_invars_str))
        [ref_loc] = re.findall(r'\d+', ref_case)
        (nla, if_ou, else_ou) = nla_ou[ref_loc]

        if 'if' in ref_case:
            select_or_z3 = DynSolver.select_or(if_ou, ref_invars)
            mlog.debug(f'final refined formula :\n {select_or_z3}')
            # ref_disj = And(ref_invars)
            # if_ou = [Or(And(if_ou), ref_disj)]
            if_ou = select_or_z3
            # if_ou, else_ou = DynSolver().remove_identical(if_ou, else_ou)
            nla_ou[ref_loc] = (nla, if_ou, else_ou)

            vtrace_name = f'vtrace_if_{ref_loc}'
            if_ou_str = list(map(lambda inv: Z3.to_string(inv),if_ou))
            self.replace_invars(vtrace_name, if_ou_str)

        if 'else' in ref_case:
            select_or_z3 = DynSolver.select_or(else_ou, ref_invars)
            mlog.debug(f'final refined formula :\n {select_or_z3}')
            else_ou = select_or_z3
            # if_ou, else_ou = DynSolver().remove_identical(if_ou, else_ou)
            nla_ou[ref_loc] = (nla, if_ou, else_ou)

            vtrace_name = f'vtrace_else_{ref_loc}'
            else_ou_str = list(map(lambda inv: Z3.to_string(inv),else_ou))
            self.replace_invars(vtrace_name, else_ou_str)
    
    
    def merge_vtrace(self, error_case, from_file):
        mlog.debug(f'------union vtrance from initial to generalized: {error_case}------')
        vtrace_fr = open(from_file, 'r')
        gen_fw = open(self.vtrace_genf, 'a')
        vtrace_list = vtrace_fr.readlines()
        vtrace = CM.vtrace_case(error_case)
        mlog.debug(f'------ vtrance to union: {vtrace}------')
        vtrace_len = len(vtrace_list)
        for i in range(vtrace_len):
            if vtrace in vtrace_list[i] and vtrace in vtrace_list[i+1] and (i < len(vtrace_list)-1):
                gen_fw.write(vtrace_list[i+1])
        vtrace_fr.close()
        gen_fw.close()
     

    def join_vtrace(self):
        '''merge vtrace_gen and vtrace_cex into vtrace_join
        '''
        shutil.copy(self.vtrace_genf, self.vtrace_joinf)
        fr_cex = open(self.vtrace_cexf, 'r')
        cex_lines = fr_cex.readlines()
        fw_join = open(self.vtrace_joinf, 'a')
        for line in cex_lines[1:]:
            fw_join.write(line)
        fr_cex.close()
        fw_join.close()

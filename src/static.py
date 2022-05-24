import re
from enum import Enum
from utils import settings, common
from utils.cparser import *

mlog = common.getLogger(__name__, settings.logger_level)


class StaticResult(Enum):
    CORRECT = 1
    INCORRECT = 2
    UNKNOWN = 3

class StaticAnalysis(object):
    def __init__(self, config):
        self.source = config.src_validate
        self.linearf = config.linearf

    def replace_str(self, mystr):
        mystr = re.sub(r'!(?!=)', 'not', mystr)
        return mystr.replace("&&", "and").replace("||", "or").replace("^", "**").replace('++','+=1').strip()
            
    def get_cex(self, outp):
        cex = {}
        vdefs = []
        path = []
        error = {}
        for i in range(len(outp)):
            line=outp[i]
            model_vdef = re.search(r'\[L(\d+)\].*int\s(\w+)\s', line)
            model_path = re.search(r'\[L(\d+)\].*COND\s(\w+)\s+(.*)', line)
            model_error = re.search('\[L(\d+)\].*reach_error', line)

            if model_vdef:
                line_info={}
                location, vdef = model_vdef.groups()
                mlog.debug(f'-----loc:{location}, variable:{vdef}\n')
                line_info['loc'] = location
                line_info['vdef'] = vdef
                vdefs.append(line_info)
            if model_path:
                line_info={}
                location, condition, expression = model_path.groups()
                mlog.debug(f'------loc:{location}, cond:{condition}, expr:{expression}')
                line_info['loc'] = location
                line_info['cond'] = condition
                line_info['exp'] = self.replace_str(expression)
                mregex = r'(\w+)=(-?\d+)'
                model_val = re.findall(mregex, outp[i+1])
                line_info['val'] = model_val
                path.append(line_info)
            if model_error:
                location = model_error.groups()
                error['loc'] = location
                error['exp'] = 'reach_error()' 
                mregex = r'(\w+)=(-?\d+)'
                model_val = re.findall(mregex, outp[i+1])
                error['val'] = model_val
        cex['vdefs'] = vdefs
        cex['path'] = path
        cex['error'] = error
        return cex
    
    def get_cex_text(self, outp):
        cex = []
        for line in outp:
            model_loc = re.search(r'\[L\d+\]', line)
            model_val = re.search(r'VAL', line)
            if model_loc or model_val:
                cex.append(line)
        return '\n'.join(cex)

    def parse_result(self, outp):
        result_str = ""
        for line in outp:
            if "RESULT:" in line:
                result_str = line
        if "incorrect" in result_str:
            # cex = self.getCex(outp)
            cex_text = self.get_cex_text(outp)
            result = StaticResult.INCORRECT
            return result, cex_text
        elif "correct" in result_str:
            result = StaticResult.CORRECT
            return result, ''
        else:
             # cex = self.getCex(outp)
            cex_text = self.get_cex_text(outp)
            mlog.debug(f'unknown result, unable to prove counterexample: \n {cex_text}') 
            result = StaticResult.UNKNOWN
            return result, cex_text

     
    def run_reach(self, source):
        mlog.info(f'------run Ultimate static analysis(reach):------')
        reach_cmd = settings.Static.run_reach(source)
        outp = common.run_cmd(reach_cmd).splitlines()
        return self.parse_result(outp)
    
    def run_term(self):
        mlog.info(f'------run Ultimate static analysis(termination):------')
        term_cmd = settings.Static.run_term(self.linearf)
        outp = common.run_cmd(term_cmd).splitlines()
        return self.parse_result(outp)
        
    def run_ltl(self):
        mlog.info(f'------run Ultimate static analysis(ltl):------')
        ltl_cmd = settings.Static.run_ltl(self.linearf)
        outp = common.run_cmd(ltl_cmd).splitlines()
        return self.parse_result(outp)
    

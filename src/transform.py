from utils import settings, common
from solver import *

mlog = common.getLogger(__name__, settings.logger_level)

class CTransform(object):
    def __init__(self, config):
        self.source = config.inp
        self.invars = config.invars_refine
        self.instr = config.src_instr
        self.validate = config.src_validate
        
    def dtrans(self, nla_ou):
        dtrans_cmd = settings.Cil.dtrans(self.source)
        mlog.info(f'------run CIL instrument for dynamic analysis:------')
        outp = common.run_cmd(dtrans_cmd)
        print(outp)
        nla_info = outp.splitlines()[1]
        nla = (nla_info.split(':')[1]).split(',')
        nla_ou[nla[0].strip()]=(DynSolver.parse(nla[1].strip()), [], [])
        
        mlog.info(f'------nla expression output:\n {nla_ou}')
  
    def strans(self):
        strans_cmd = settings.Cil.strans(self.source, self.invars)
        mlog.info(f'------run CIL instrument for static analysis:------')
        common.run_cmd(strans_cmd)
  
    def vtrans(self, pre, case):
        vtrans_cmd = settings.Cil.vtrans(self.source, self.invars, pre, case)
        mlog.info(f'------run CIL instrument with predicate:------\n')
        common.run_cmd(vtrans_cmd)
  

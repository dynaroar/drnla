from utils import settings, common
from solver import *

mlog = common.getLogger(__name__, settings.logger_level)
 
class CTransform(object):
    def __init__(self, config):
        self.origin = config.origin
        self.source = config.inp
        self.invars = config.invars_refine
        self.ouf = config.ou_mapf
        self.instr = config.src_instr
        self.validate = config.src_validate
        
    def dtrans(self, nla_ou):
        dtrans_cmd = settings.Cil.dtrans(self.source)
        mlog.info(f'------run CIL instrument for dynamic analysis:------')
        outp = common.run_cmd(dtrans_cmd)
        nla_info = outp.splitlines()[1]
        nla = (nla_info.split(':')[1]).split(',')
        try:
            nla_ou[nla[0].strip()]=(DynSolver.parse(nla[1].strip()), [], [])
        except IndexError:
            mlog.error(f'----No nla expression found in main() for {self.origin}')
            mlog.error(f'----cmd:{dtrans_cmd}')
            sys.exit()
        
        mlog.info(f'------nla expression output:\n {nla_ou}')
  
    def strans(self):
        strans_cmd = settings.Cil.strans(self.source, self.invars)
        mlog.info(f'------run CIL instrument for static analysis(validation for OU):------')
        common.run_cmd(strans_cmd)
  
    def vtrans(self, pre, case):
        vtrans_cmd = settings.Cil.vtrans(self.source, self.invars, pre, case)
        mlog.info(f'------run CIL instrument with predicate:------\n')
        common.run_cmd(vtrans_cmd)
  
    def ltrans(self):
        ltrans_cmd = settings.Cil.ltrans(self.origin, self.ouf)
        mlog.info(f'------run CIL instrument with OU substitution for verification :------\n')
        common.run_cmd(ltrans_cmd)

        

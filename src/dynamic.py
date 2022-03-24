
from utils import settings, common

class DynamicAnalysis(object):
    def __init__(self, config):
        self.source = config.src_instr
        self.invarsf = config.invarsf
        self.vtracef = config.vtracef
        self.vtrace_processed = config.vtrace_processed
    def runTrace(self):
        vtrace_cmd = settings.Dynamic.vtrace_run(self.vtrace_processed, self.invarsf)
        # mlog.info(f'------run DIG dynamic on vtrace file:------') 
        common.runCmd(vtrace_cmd)
    def runSource(self):
        source_cmd = settings.Dynamic.source_run(self.source, self.invarsf, self.vtracef)
        # mlog.info(f'------run DIG dynamic with source file:-------')
        common.runCmd(source_cmd)
  

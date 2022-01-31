import tempfile
import os

from utils import settings, common
from pathlib import Path
 
mlog = common.getLogger(__name__, settings.logger_level)

class Setup(object):
    def __init__(self, inp):
        self.inp = inp
        self.invar = settings.invars
        self.is_c_inp = inp.endswith(".c")
        self.tmpdir = Path(tempfile.mkdtemp(dir=settings.tmpdir, prefix="dltl_"))
        self.trans_out = self.tmpdir / (os.path.basename(inp))
        self.symstates = None
        assert (self.is_c_inp), "\n Please input a C program: "+ inp
        
class GENTRACE(object):
    def __init__(self, config):
        self._config = config
        self.nonlinear_loc = []
    def gen(self):
        _config = self._config
        mlog.info("instrument source file and compile to run.")

class CINSTR(object):
    def __init__(self, config):
        self._config = config
    def transform(self):
        _config = self._config
        source = _config.inp
        # trans_outf = _config.tmpdir / (os.path.basename(source))
        trans_outf = _config.trans_out
        assert_invar = _config.invar 
        trans_cmd = settings.CIL.TRANSFORM(inf=source,
                                           invar=assert_invar)
        mlog.info(f'run CIL instrument on {trans_cmd} ... \n {trans_outf}')

class DIG(object):
    
    def __init__(self, config):
        self._config = config
        # self._transf = Path(config.trans_out)
        self.invarsf = config.tmpdir / 'dltl.inv'
    def run(self):
        source = self._config.trans_out
        run_cmd = settings.DYNAMIC.RUN_CMD(filename=source, invart_outf=self.invarsf)
        mlog.info(f'run DIG dynamic with command:\n {run_cmd}')
         

class ULTIMATE(object):
    def __init__(self, config):
        self._config = config
    def run(self):
        source = self._config.trans_out
        run_cmd = settings.ULTIMATE.RUN_CMD(filename=source)
        mlog.info(f'run ULTIMATE with command:\n {run_cmd}')

    
        
    

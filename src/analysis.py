import tmpfile

from utils import settings, common
from pathlib import Path
 
mlog = common.getLogger(__name__, settings.logger_level)

class Setup(object):
    def __init__(self, inp):
        self.inp = inp
        self.is_c_inp = inp.endswith(".c")
        self.tmpdir = Path(tempfile.mkd(dir=settings.tmdir, prefix="dltl_"))
        self.symstates = None
        assert (self.is_c_inp), inp

        
        
        
    


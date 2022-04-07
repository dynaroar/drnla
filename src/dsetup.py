import tempfile
import os, re, ast
import subprocess, shlex
from pathlib import Path
import shutil

from utils import settings, common

mlog = common.getLogger(__name__, settings.logger_level)

class Setup(object):
    # source_path= []
    # # mlog.debug(f'source_path:\n {self.source_path}')
    # src_instr = "_instr.c"
    # src_validate = "_validate.c"
    # invarsf = ".inv"
    # invars_refine = "_refine.inv"
    # vtracef = ".csv"
    # vtrace_genf = "_gen.csv"
    # vtrace_cexf = "_cex.csv"
    
    def __init__(self, inp):
        self.is_c_inp = inp.endswith(".c")
        assert (self.is_c_inp), "\n Please input a C program: "+ inp
        
        self.tmpdir = Path(tempfile.mkdtemp(dir=settings.tmpdir, prefix="dltl_"))
        shutil.copy(inp, self.tmpdir)

        self.input_base = os.path.basename(inp)
        self.input_name, _ = str(self.input_base).split('.')
        self.inp = str(self.tmpdir/self.input_base)
        self.vtracef = str(self.tmpdir/self.input_name) + ".csv"

        self.symstates = None
        self.init_files()


    def init_files(self):
        self.source_path= self.inp.split(".")
        # mlog.debug(f'source_path:\n {self.source_path}')
        self.src_instr = self.source_path[0] + "_instr.c"
        self.src_validate = self.source_path[0] + "_validate.c"
        self.invarsf = self.source_path[0] + ".inv"
        self.invars_refine = self.source_path[0] + "_refine.inv"
        # self.vtracef = self.source_path[0] + ".csv"
        self.vtrace_genf = self.source_path[0] + "_gen.csv"
        self.vtrace_cexf = self.source_path[0] + "_cex.csv"
        self.vtrace_joinf = self.source_path[0] + "_join.csv"

    def update_basename(self, iter):
        input_file = self.tmpdir/Path(self.input_name + '_refine'+ str(iter) + '.c')
        shutil.copy(self.inp, input_file)
        self.inp = str(input_file)

        invars_refine = self.tmpdir/Path(self.input_name + '_refine' + str(iter) + '_refine.inv')
        shutil.copy(self.invars_refine, (invars_refine))
         
        self.init_files()
         

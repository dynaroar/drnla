#!/usr/bin/python3

import re
import sys
import os
import subprocess
import argparse
import numpy as np
import shlex
import shutil
import datetime, time 
import multiprocessing as mp

import analysis

from random import randrange, randint, seed
from functools import reduce
from itertools import groupby
from enum import Enum
from utils import settings, common

dynamltl_path = os.path.realpath(os.path.dirname(__file__))
dig_path = os.path.realpath(os.path.join(dynamltl_path, '../deps/dig/src'))
sys.path.insert(0, dig_path)



  
if __name__ == "__main__":
    aparser = argparse.ArgumentParser(description='Dynamltl', prog='dynamltl')
    ag = aparser.add_argument
    ag("--inp", "-i",
       type=str,
       help="input c program")
  
    # ag("--gen_tcs", "-gen_tcs",
    #    action="store_true",
    #    help="generate traces with random inputs.")
    
    ag("--init-ou", "-init",
       action = "store_true",
       help="initial OU mapping for IF ELSE")

    ag("--bv", "-bv",
       action= 'store_true',
       help= 'flag to run initial dynamic analysis on the input directly')
   
    ag("--log", "-log",
       type=int,
       choices=range(5),
       default=4,
       help="set logger level info")
  
    ag("--timeout", "-timeout",
       type=int,
       default=600,
       help="set timeout (s)")

    ag("--refine", "-refine",
       type=int,
       default=4,
       help="set the number of refinement iteration")

    ag("--snaps", "-snaps",
       type=int,
       default=1000,
       help="set the number of snaps/model in cex generalization")

    ag("--repeat", "-repeat",
       type=int,
       default=50,
       help="set the repeat bound for the same variable sanp")

    ag("--upper", "-upper",
       type=int,
       default=20,
       help="set the upper bound for normalized template invriants")

    ag("--lbnd", "-lbnd",
       type = int,
       nargs = '?',
       const = 500,
       help="set loop bound for non-terminating loop")

    ag("--prop", "-prop",
       type=str,
       default='reach',
       choices= settings.props_list,
       help= f'select which property to verify')

    ag("--verdict", "-verdict",
       type=str,
       default= settings.verdict,
       help= f'user provided desired IF condition')
    
    ag("--tmpdir", "-tmpdir",
       type=str,
       default= settings.tmpdir,
       help= f'set temporary path for intermediate files')

    
    args = aparser.parse_args()

    if args.init_ou:
        settings.init_ou = args.init_ou
        
    if args.lbnd is not None:
        settings.is_lbnd = True
        settings.lbnd = args.lbnd
 
        
    settings.timeout = args.timeout    
    settings.logger_level = args.log
    settings.refine = args.refine
    settings.snaps = args.snaps
    settings.repeat = args.repeat
    settings.uppper = args.upper
    settings.prop = args.prop
    settings.tmpdir = args.tmpdir
    settings.verdict = args.verdict
    settings.bv = args.bv
  
    inp = os.path.realpath(os.path.expanduser(args.inp))

    mlog = common.getLogger(__name__, settings.logger_level)
    mlog.info(f'DynamLTL log level: {settings.logger_level}')
    mlog.info(f'Timeout: {settings.timeout}s')
    mlog.info(f'{datetime.datetime.now()}, {sys.argv}')

    config = analysis.Setup(inp)
    mlog.info(f'analysis files stored in: {config.tmpdir}')
 
    ou_analysis = analysis.OUAnalysis(config)

    def simplify():
        ou_analysis.nla_run()            

    def prove():
        ou_analysis.verify_run()

    def func_time(func):
        start = time.time()
        func()
        end = time.time()
        return (end-start)
    
    ts = func_time(simplify)
    ta = ts+func_time(prove)

    # map_str = f'MAP: to be converted'
    steps_str = 'REFINEMENT:' + ' -> '.join(ou_analysis.refine_steps)
    init_map = f'INITIAL-OU:{ou_analysis.ou_init_str}'
    final_map = f'FINAL-OU:{ou_analysis.ou_str}'
    prop_str =f'PROPERTY:{settings.prop}'
    result = f'RESULT:{ou_analysis.verify_result}'
    time_simp = f'TIME-SIMPLIFICATION:{ts}s' 
    time_all = f'TIME-TOTAL:{ta}s'

    details_str = f'{steps_str} \n {init_map} \n {final_map}\n {prop_str}\n {result}'
    time_str = f'{time_simp} \n {time_all} \n'
    mlog.info(f'----DynamiteLTL Analysis Result:----\n {details_str} \n {time_str}')
    # print(f'----DynamiteLTL Analysis Result:----\n {details_str} \n {time_str}')
 
    
    # prove_process = mp.Process(target=simplify)
    # prove_process.start()
    # mlog.debug('prove_process: {}'.format(prove_process.pid))
    # prove_process.join(timeout=settings.timeout)


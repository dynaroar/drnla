#!/usr/bin/python3

import re
import sys
import os
import subprocess
import argparse
import numpy as np
import shlex
import shutil
import datetime, multiprocessing

import analysis

from random import randrange, randint, seed
from functools import reduce
from itertools import groupby
from enum import Enum
from utils import settings, common

# A main driver to run the sub-components.

    
if __name__ == "__main__":
    aparser = argparse.ArgumentParser(description='Dynamltl', prog='dynamltl')
    ag = aparser.add_argument
    ag("--inp", "-i",
       type=str,
       help="input c program")
    
    ag("--n", "-n",
       type=int,
       default=20,
       help="numbers of program executions")
    
    ag("--vs", "-v",
       type=str,
       help="invariants file from Dig.")

    ag("--gen_tcs", "-gen_tcs",
       action="store_true",
       help="generate traces with random inputs.")
    
    ag("--log", "-log",
       type=int,
       choices=range(5),
       default=4,
       help="set logger level info")
  
    ag("--timeout", "-timeout",
       type=int,
       default=300,
       help="set timeout")

    args = aparser.parse_args()

    if args.timeout:
        settings.timeout = int(args.timeout)
        
    settings.logger_level = args.log
    settings.gen_tcs = args.gen_tcs
    inp = os.path.realpath(os.path.expanduser(args.inp))

    mlog = common.getLogger(__name__, settings.logger_level)
    mlog.info(f'DynamLTL log level: {settings.LoggerLevel}')
    mlog.info(f'Timeout: {settings.TimeOut}s')
    mlog.info(f'{datetime.datetime.now()}, {sys.argv}')

    # main(args.inp, args.n, args.vs)
    config = analysis.Setup(inp)

    def prove():
        ou = analysis.OUAnalysis(config)
        result, nla_ou = ou.run()            
        mlog.info(f'OU analysis result: \n {result}\n nla mapping:\n {nla_ou}')
    prove_process = multiprocessing.Process(target=prove)
    prove_process.start()
    mlog.debug('prove_process: {}'.format(prove_process.pid))
    prove_process.join(timeout=settings.timeout)


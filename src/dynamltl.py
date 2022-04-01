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
       help="initial OU mapping for IF ELSE.")

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

    if args.init_ou:
        settings.init_ou = args.init_ou
    if args.timeout:
        settings.timeout = int(args.timeout)
        
    settings.logger_level = args.log
  
    inp = os.path.realpath(os.path.expanduser(args.inp))

    mlog = common.getLogger(__name__, settings.logger_level)
    mlog.info(f'DynamLTL log level: {settings.logger_level}')
    mlog.info(f'Timeout: {settings.timeout}s')
    mlog.info(f'{datetime.datetime.now()}, {sys.argv}')

    config = analysis.Setup(inp)
    mlog.info(f'analysis files stored in: {config.tmpdir}')
 
    def prove():
        ou = analysis.OUAnalysis(config)
        ou.run()            
        mlog.info(f'OU analysis result: {ou.result}\n nla mapping:\n {ou.nla_ou}')
    prove_process = multiprocessing.Process(target=prove)
    prove_process.start()
    mlog.debug('prove_process: {}'.format(prove_process.pid))
    prove_process.join(timeout=settings.timeout)


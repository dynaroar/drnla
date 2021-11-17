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

from random import randrange, randint, seed
from functools import reduce
from itertools import groupby
from enum import Enum
from utils import settings, common
# A main driver to run the sub-components.

dynamltl_path = os.path.realpath(os.path.dirname(__file__))
dig_path = os.path.realpath(os.path.join(dynamltl_path, '../deps/dig/src'))
instr_path = os.path.realpath(os.path.join(dynamltl_path, '../deps/sourceInstr/'))

sys.path.insert(0, dig_path)
sys.path.insert(0, instr_path)


    
# def main (program, iter_num, predicate, value):
# def main (program, iter_num, invs):
#     #run the program with random number to generate traces
#     # init_prog(program)
#     # traces = gettcs(program, iter_num)
#     invars = parse_results(invs)
#     print("parse all invariants into a list:")
#     print('\n'.join(map(str, invars)))
  
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
    
    ag("--log", "-log",
       type=int,
       choices=range(5),
       default=4,
       help="set logger level info")
    
    # ag("--run_dig", "-run_dig", action="store_true", help="run DIG on the input")

    ag("--timeout", "-timeout",
       type=int,
       default=300,
       help="set timeout")

    args = aparser.parse_args()

    if args.timeout:
        settings.timeout = int(args.timeout)
        
    settings.logger_level = args.log
    
    inp = os.path.realpath(os.path.expanduser(args.inp))

    mlog = common.getLogger(__name__, settings.logger_level)
    mlog.info(f'DynamLTL log leverl: {settings.logger_level}')
    mlog.info(f'Timeout: {settings.timeout}s')
    mlog.info(f'{datetime.datetime.now()}, {sys.argv}')

    # main(args.inp, args.n, args.vs)
    def prove():
        pass
    prove_process = multiprocessing.Process(target=prove)
    prove_process.start()
    mlog.debug('prove_process: {}'.format(prove_process.pid))
    prove_process.join(timeout=settings.timeout)

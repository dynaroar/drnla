#!/usr/bin/python3

import re
import sys
import os
import subprocess
import argparse
import numpy as np
import shlex
import shutil
from random import randrange, randint, seed
from functools import reduce
from itertools import groupby
# sys.path.append("../tools")
# import time

from enum import Enum
  
# compile and run c program to generate traces, store trace data into a hash table.
def gettcs(prog, iter):
    """run .
    Args:
        prog: c program source code.
        iter: numbers of program executions.
     """
    (progpath, progbase) = os.path.split(prog)
    file_name = progbase.split(".")
    progname = file_name[0]
    compile_cmd=f"gcc {prog} -o {progpath}/{progname}"
    subprocess.run(shlex.split(compile_cmd), capture_output=True, check=True, text=True)

    trace_path = f"{progpath}/traces"
    if not os.path.exists(trace_path):
        os.makedirs(trace_path)
    else :
        shutil.rmtree(trace_path)
        os.makedirs(trace_path)
    tracehash = {}
    for i in range(iter):
        trace_file = f"{trace_path}/{progname}_{i}.tcs"
        nondet_input = randint(-100, 100)
        with open(trace_file, 'w+') as f:
            subprocess.call(['./' + progpath +'/'+ progname, str(nondet_input)], stdout=f)
            data_traces = []
            f.seek(0)
            for line in f:
                itemList = re.split(",", line.rstrip('\n'))
                numList = list(map (lambda x: int(x.strip()), itemList))
                data_traces.append(numList)
        tracehash[i] = data_traces
    return tracehash
      
         
def main(program, iter_num, predicate, value):
    #run the program with random number to generate traces
    traces = gettcs(program, iter_num)
    print (f"traces: {traces}")
    return None

if __name__ == "__main__":
    aparser = argparse.ArgumentParser("Run c program to collect traces.")
    ag = aparser.add_argument
    ag("--inp", "-i", type=str, help="input c program")
    ag("--n", "-n", type=int, default=20, help="numbers of program executions")
    ag("--p", "-p", type=int, help="which data point to check?")
    ag("--v", "-v", type=int, help="what value the data point checks against?")
    args = aparser.parse_args()
    main(args.inp, args.n, args.p, args.v)

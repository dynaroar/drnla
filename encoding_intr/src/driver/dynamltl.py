#!/usr/bin/python3

import re
import sys
import os
import subprocess
import argparse
import numpy as np
import networkx as nx
import matplotlib.pyplot as plt
import shlex
import shutil

from random import randrange, randint, seed
from functools import reduce
from itertools import groupby
from enum import Enum
 
# A main driver to run the sub-components.

def init_prog (program):
    pass

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
    # tracehash = {}
    trace_file = f"{trace_path}/{progname}.tcs"
    fw = open(trace_file, "w")
    # print("vtrace28; I x; I y; I c", file=fw)
    # print("vtrace25; I x; I y; I c", file=fw)

    for i in range(iter):
        # trace_file = f"{trace_path}/{progname}_{i}.tcs"
        nondet_input = randint(-50, 50)
        # with open(trace_file, 'w+') as f:
        subprocess.call(['./' + progpath +'/'+ progname, str(nondet_input), "0"], stdout=fw)
    # print("vtrace28; I x; I y; I c", file=fw)
    fw.close()
    print("trace generated!")

def run_dig (traces):
    pass


def parse_results(file_invs):
    fr = open(file_invs, "r")
    invsList = []
    for line in fr:
        itermList = re.split(";", line.rstrip('\n'))
        invsList = invsList + itermList
    return invsList

def run_instr(program, invars):
    pass
    
def run_ultimate (program):
    pass
    
    
# def main (program, iter_num, predicate, value):
def main (program, iter_num, invs):
    #run the program with random number to generate traces
    # init_prog(program)
    # traces = gettcs(program, iter_num)
    invars = parse_results(invs)
    print("parse all invariants into a list:")
    print('\n'.join(map(str, invars)))
  
if __name__ == "__main__":
    aparser = argparse.ArgumentParser("Run c program to collect traces.")
    ag = aparser.add_argument
    ag("--inp", "-i", type=str, help="input c program")
    ag("--n", "-n", type=int, default=20, help="numbers of program executions")
    ag("--vs", "-v", type=str, help="invariants file from Dig.")
    # ag("--v", "-v", type=int, help="what value the data point checks against?")
    args = aparser.parse_args()
    # main(args.inp, args.n, args.p, args.v)
    main(args.inp, args.n, args.vs)

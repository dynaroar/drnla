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

def run_command(command):
    try:
        p = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300.0)
    except subprocess.TimeoutExpired as e_timeout:
        error = "-----Time Out(300s)----\n"
        return error.encode('utf-8')
    return p.stdout




# read and parse traces data into matrix and analyze them finding the backward recent common trace.
def analyze_traces(traces, var, val):
    """run .
    Args:
        traces: c program execution traces data.
        var: predicate value to check, recorded as index to data point.
    """
    predholds=[]
    for datafile in os.listdir(traces):
        with open(f"{traces}/{datafile}", "rt") as fr:
            data_traces = []
            for line in fr:
                itemList = re.split(",", line.rstrip('\n'))
                numList = list(map (lambda x: int(x.strip()), itemList))
                data_traces.append(numList)
                # data_traces.append(itemList)
        data_traces = np.matrix(data_traces)
        var_col = sum(data_traces[:,var].tolist(),[])
        trace_col = sum(data_traces[:,0].tolist(),[])

        # var_col =[row[var] for row in data_traces]
        # preds = list(filter (lambda x: x==0, var_col))

        predindex = []
        tracehold = []
        for i in range(len(var_col)):
            if var_col[i] == val and i != 0:
                predindex.append(i)
                tracehold = trace_col[:i+1]
                break
        tracehold.reverse()
        predholds.append(tracehold)

        print(f"----matrix from {datafile}-----\n" + str(data_traces.shape))
        print(data_traces)

        # print(var_col)
        print(f"atomic property holds at: {predindex}")
        print(f"trace location reached to this hold position:\n{tracehold}")
    print("all runs that reach the state where predicate holds:")
    print(predholds)

# cut off to the length of mininal trace:
    trace_length = list(map(lambda x: len(x), predholds))
    # if not trace_length and 0 == trace_length:
    #     return -1
    # minlen = min([value for value in trace_length if value != 0])
    print(trace_length)
    # print(f"The shortest trace run state number: {minlen}")

    submatrix=[]
    print("predicate holds on non-empty traces for all the runs:")
    for iterm in predholds:
        if iterm:
            print(iterm)
            # subtrace = iterm[]
            # submatrix.append(iterm[:minlen])
            submatrix.append(iterm)

    if submatrix:
        # subarray = np.array(submatrix)
        # truecol =np.all(subarray == subarray[0,:], axis = 0)
        # print(truecol)
        # comval = -1
        # trans_trc = (np.matrix(submatrix)).T
        # for i in range(trans_trc.shape[0]):
        #     if np.all(trans_trc[i] == trans_trc[i][0]):
        #         print('All run holds recently at Column:', i)
        #         comval = trans_trc[i][0]
        #         return comval
        #     else:
        #         return -1
        # commontcs = list(set.intersection(*map (set, submatrix)))
        noreptcs = []
        for i in range(len(submatrix)):
            norep = [i[0] for i in groupby(submatrix[i])]
            noreptcs.append(norep)
        print("predicate holds with no repeating traces:\n" + str(noreptcs))

        if len(noreptcs) >= 2:
            commonloc = 1
            for ele in noreptcs[0]:
                iscontained = list(map (lambda tcs: ele in tcs, noreptcs[1:]))
                print("the first traces element is conrained :" + str(iscontained))
                if all(iscontained):
                    commonloc = ele
                    break
            return commonloc
        else:
            return submatrix[0][0]

    else :
        return -1




# compile and run c program to generate traces
def run_prog(prog, iter, pred, val):
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
    for i in range(iter):
        trace_file = f"{trace_path}/{progname}_{i}.tcs"
        nondet_input = randint(-100, 100)
        with open(trace_file, 'w') as f:
            subprocess.call(['./' + progpath +'/'+ progname, str(nondet_input)], stdout=f)
    comloc = analyze_traces(trace_path, pred, val)
    print(f"The latest common trace location is(-1 meaning not existing): {comloc}")


def main(program, iter_num, predicate, value):
    #run the program with random number to generate traces
    run_prog(program, iter_num, predicate, value)
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

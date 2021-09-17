#!/usr/bin/python3

import re
import sys
# import os
# import subprocess
import argparse
import numpy as np
import networkx as nx
import matplotlib.pyplot as plt
import shlex
import shutil

from pyModelChecking import *
from random import randrange, randint, seed
from functools import reduce
from itertools import groupby
from enum import Enum

# sys.path.append("../tools")
# import time

# import local modules
import ltl as L
import utils as U



def transi(traces_hash):
    rungraph = dict()
    varshash = dict()
    for run, traces in traces_hash.items():
        G = nx.DiGraph()
        traceTuple = list(map(lambda x:tuple(x), traces))
        # map variable name to it's trace data location(columns)
        for i in range(len(traceTuple[0])):
            varshash[U.vars_name[i]]= i
        for i in range(len(traceTuple)-1):
            pre, succ = (traceTuple[i], traceTuple[i+1])
            G.add_edge(pre, succ)
        rungraph[run] = G
    return rungraph, varshash

 

def checkLTL(trace_graph, phi, aps):
    ctlgraph = {} 
    for key, G in trace_graph.items():
        pass
    ctlgraph[key] = G
    return ctlgraph
 


def getResult(result_graph):
    resutls = {}
    hold = True
    cex = (None, None)
    for key, rgraph in result_graph.items():
        hold = rgraph.graph['Fp']['holds'] and hold 
        if not (rgraph.graph['Fp']['holds']):
            hold = False;
            cex = (key, None)
            break
    results = {"Holds": hold, "CEX": cex}
    return results        
        
 
   
def main (program, iter_num, predicate, value):
    #run the program with random number to generate traces
    # atomic proposition, a dictionary from name to value.
    traces = U.gettcs(program, iter_num)
    tracegraph, vars = transi(traces)
    print(f"vars name from data trace: {vars}")
    atomicHash = dict()
    atomicHash['p'] = 'x<0'
    atomicHash['q'] = 'y==0'
    atomic1 = L.AtomicProposition('p')
    atomic2 = L.AtomicProposition('q')
    phiR = L.F(atomic2)
    phi1 = L.Or(atomic1, phiR)
    phi = L.G(phi1)
    resultgraph = checkLTL(tracegraph, phi, atomicHash)

    # for key, graph in tracegraph.items():
    #     print(f"----run {key} of nodes data:\n {graph.nodes(data=True)} \n")
    #     print(f"----run {key} of results:\n {graph.graph} \n")
    # results = getResult(resultgraph)
    # print(f"The Property AF(y==0) holds for the input program: {results}")
    # U.drawG(tracegraph)
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

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
from z3 import *

# sys.path.append("../tools")
# import time

# import local modules
import ltl as L
import utils as U

varsName = [Int('loc'), Int('x'), Int('y'), Int('z'), Int('a'), Int('b'), Int('c')]

def z3check(f):
    s = Solver()
    s.add(Not(f))
    if s.check() == unsat:
        return True
    else:
        print (f"failed to prove formula sat: {f}")
        print(s.model())
        return False

def transi(traces_hash):
    rungraph = dict()
    # varshash = dict()
    for run, traces in traces_hash.items():
        G = nx.DiGraph()
        traceTuple = list(map(lambda x:tuple(x), traces))
        # map variable name to it's trace data location(columns)
        # for i in range(len(traceTuple[0])):
        #     varshash[i]= Int(U.vars_name[i])
        for i in range(len(traceTuple)-1):
            pre, succ = (traceTuple[i], traceTuple[i+1])
            G.add_edge(pre, succ)
        rungraph[run] = G
    # return rungraph, varshash
    return rungraph


def resetL(trace, f):
    for node in trace.nodes:
        for subf in f:
            nx.set_node_attributes(trace, {node: False}, subf)            
    
def nodesat(node, ap_value):
    
    nodeVal = And(True, True)
    for i in range(len(list(node))):
        if i != 0:
            nodeVal = And(varsName[i] == node[i], nodeVal)
    fz3 = Implies(nodeVal, ap_value)
    z3sat = z3check(fz3)
    # print(f"check z3 formula for node {node}: {fz3}")
    # print(f"results: {z3sat}")
    return z3sat 


def setPre(trace, f, index):
    nodeUpdate = list(trace.nodes)[:index]
    for node in nodeUpdate:
        trace.nodes[node][f] = True
        
def labelT(trace, f):

    for subf in f:
        # trace_rev = nx.DiGraph.reverse(trace)
        nodes_rev = list(trace.nodes)[::-1]

        # print(f"trace_rev nodes: {nodes_rev}")
       
        for node in nodes_rev:
            # if isinstance(subf, L.AtomicProposition) and (node[0] != 1):
            if isinstance(subf, L.AtomicProposition):
                # ap_value = aps[subf.name]
                ap_value = subf.atom
                if nodesat(node, ap_value):
                    trace.nodes[node][subf] = True
                    
            if isinstance(subf, L.F):
                subff = subf.subformula
                if trace.nodes[node][subff]:
                    trace.nodes[node][subf] = True
                    index = list(trace.nodes()).index(node)
                    print(f"node in nodes index: {list(trace.nodes()).index(node)}")
                    setPre(trace, subf, index)
                    break
                    
            if isinstance(subf, L.G):
                subff = subf.subformula
                # only set trues for all the nodes that all subff are true.
                if trace.nodes[node][subff]:
                    # index = nodes_rev.index(node)
                    # for item in nodes_rev[index:]:
                    #     i = nodes_rev.index(item)
                    #     if i == 0:
                    #     trace.nodes[item][subf] = True
                    # elif trace.nodes[item][subff] and trace.nodes[nodes_rev[i-1]][subf]:
                    #     trace.nodes[item][subf] = True
                    # else:
                    #     break
                    trace.nodes[node][subf] = True
                else:
                    break
            
            if isinstance(subf, L.Or):
                subf1 = subf.left
                subf2 = subf.right
                if trace.nodes[node][subf1] or trace.nodes[node][subf2]:
                    trace.nodes[node][subf] = True
                    
            if isinstance(subf, L.And):
                subf1 = subf.left
                subf2 = subf.right
                if trace.nodes[node][subf1] and trace.nodes[node][subf2]:
                    trace.nodes[node][subf] = True
    # trace = nx.DiGraph.reverse(trace_rev)
         
                  

def checkLTL(trace_graph, phis):
    ctlgraph = {} 
    for key, G in trace_graph.items():
        resetL(G, phis)
        labelT(G, phis)
    ctlgraph[key] = G
    return ctlgraph
 


def getResult(result_graph, phiLtl):
    resutls = {}
    hold = True
    cex = (None, None)
    for key, rgraph in result_graph.items():
        subhold = True
        for node in rgraph.nodes:
            subhold = rgraph.nodes[node][phiLtl] and subhold
                    
        hold = subhold and hold 
    results = {"Holds": hold, "CEX": cex}
    return results        
        
  
# def main (program, iter_num, predicate, value):
def main (program, iter_num):
    #run the program with random number to generate traces
    # atomic proposition, the formula type is now a Z3.ast.
    traces = U.gettcs(program, iter_num)
    # tracegraph, vars = transi(traces)
    tracegraph = transi(traces)
    # print(f"vars z3 name from data trace: {vars}")

    # subfs = U.initTest()
    # subfs = U.test1()  
    # subfs = U.test2()  
    subfs = U.test3()  
    print(f"before model checking formla: {subfs}")
    resultgraph = checkLTL(tracegraph, subfs)

    for key, graph in tracegraph.items():
        if key == 0:
            print(f"----run {key} of nodes data:\n {graph.nodes(data=True)} \n")
    #     print(f"----run {key} of results:\n {graph.graph} \n")
    results = getResult(resultgraph, subfs[-1])
    print(f"The Property {subfs[-1]} holds for the input program: {results}")
    # U.drawG(tracegraph)
    return None

if __name__ == "__main__":
    aparser = argparse.ArgumentParser("Run c program to collect traces.")
    ag = aparser.add_argument
    ag("--inp", "-i", type=str, help="input c program")
    ag("--n", "-n", type=int, default=20, help="numbers of program executions")
    # ag("--p", "-p", type=int, help="which data point to check?")
    # ag("--v", "-v", type=int, help="what value the data point checks against?")
    args = aparser.parse_args()
    # main(args.inp, args.n, args.p, args.v)
    main(args.inp, args.n)

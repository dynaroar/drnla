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

# bottom up a ltl formula, collect all the sub formulas

     # G(AP(x<0) Or F(AP(y==0))), default the order, <s
    # atomic1 = L.AtomicProposition('x<0')
    # atomic2 = L.AtomicProposition('y==0')
    # phiF = L.F(atomic2)
    # phiOr = L.Or(atomic1, phiF)
    # phiG = L.G(phiOr)
    # subfs = [atomic1, atomic2, phiF, phiOr, phiG]

def initFormulas(phi, subfs):
    if isinstance(phi, L.AtomicProposition):
        return subfs

    elif isinstance(phi, L.F):
        sf = phi.subformula
        subfs = [sf] + subfs
        # print(f"subformula in F: {subfs}")
        return initFormulas(sf, subfs)
      
    elif isinstance(phi, L.G):
        sf = phi.subformula
        subfs = [sf] + subfs
        # print(f"subformula in G: {subfs}")
        return initFormulas(sf, subfs)

    elif isinstance(phi, L.Or):
        sf1 = phi.left
        sf2 = phi.right
        subR = initFormulas(sf2, [sf2]+subfs)
        return initFormulas(sf1, [sf1]+subR)

    elif isinstance(phi, L.And):
        sf1 = phi.left
        sf2 = phi.right
        sub_R = initFormulas(sf2, [sf2]+subfs)
        initFormulas(sf1, [sf1]+subR)
    else:
        raise Exception(f"Not a valid ltl formula {str(phi)}")


def initTest():
    # aphash = dict()
    # aphash['p'] = 'x<0' # should z3 ast
    # aphash['q'] = 'y==0' # 
    # G(AP(x<0) Or F(AP(y==0))), default the order, <s
    # atomic1 = L.AtomicProposition('p')
    # atomic2 = L.AtomicProposition('q')
    atomic1 = L.AtomicProposition('x<0')
    atomic2 = L.AtomicProposition('y==0')
    phiF = L.F(atomic2)
    phiOr = L.Or(atomic1, phiF)
    phiG = L.G(phiOr)

    subfs = initFormulas(phiG, [phiG])
    # subfs = [atomic1, atomic2, phiF, phiOr, phiG]
    print(f"subformulas lists: {subfs}")
    return subfs

def resetL(trace, f):
    for node in trace.nodes:
        for subf in f:
            nx.set_node_attributes(trace, {node: False}, subf)            
    
def nodesat(node, ap_value):
    #TODO construct smt script here...    
    return True

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
        
def test1():
     pass
     
   
# def main (program, iter_num, predicate, value):
def main (program, iter_num):
    #run the program with random number to generate traces
    # atomic proposition, the formula type is now a Z3.ast.
    traces = U.gettcs(program, iter_num)
    tracegraph, vars = transi(traces)
    print(f"vars name from data trace: {vars}")

    subfs = initTest()
    print(f"before model checking formla: {subfs}")
    resultgraph = checkLTL(tracegraph, subfs)

    for key, graph in tracegraph.items():
        print(f"----run {key} of nodes data:\n {graph.nodes(data=True)} \n")
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
    # ag("--p", "-p", type=int, help="which data point to check?")
    # ag("--v", "-v", type=int, help="what value the data point checks against?")
    args = aparser.parse_args()
    # main(args.inp, args.n, args.p, args.v)
    main(args.inp, args.n)

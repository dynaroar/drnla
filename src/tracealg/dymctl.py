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
from pyModelChecking import *
from random import randrange, randint, seed
from functools import reduce
from itertools import groupby
# sys.path.append("../tools")
# import time

from enum import Enum

# draw the trace graph, default to 4 subplots
def drawG(graph):
    # for key, graph in graph.items():
    #     loc = 221 + int(key)
    #     plt.subplot(loc)
    #     # plt.figure()
    #     # nx.draw(graph, with_labels=True, font_weight='bold')
    #     labels = nx.get_node_attributes(graph, 'vars') 
    #     nx.draw(graph, labels=labels, font_weight='bold')
    nx.draw(graph, with_labels=True, node_size = 20)
    plt.show()



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
        nondet_input = randint(1, 50)
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

def transi(traces_hash):
    rungraph = {}
    # G = nx.DiGraph()
    for run, traces in traces_hash.items():
        # print(f"------run {run}--------")
        G = nx.DiGraph()
        states = [item[0] for item in traces]
        # statenorep = [i[0] for i in groupby(states)]
        for i in range(len(traces)-1):
            pre, succ = (traces[i][0], traces[i+1][0])  
            G.add_edge(pre, succ)

        # set graph node attributes to store vars concrete value
        for node in G.nodes():
            nx.set_node_attributes(G, {node:[]}, "vars")
        for item in traces:
            node = item[0]
            nodeval = item[1:]
            G.nodes[node]['vars'].append(nodeval)
            # print(f"node {node} data: {G.nodes[node]}")
        rungraph[run] = G
    return rungraph

def transiG(traces_hash, node_hash):
    # rungraph = {}
    G = nx.DiGraph()
    for run, traces in traces_hash.items():
        states = [item[0] for item in traces]

        for i in range(len(traces)-1):
            pre, succ = (tuple(traces[i]), tuple(traces[i+1]))  
            G.add_edge(pre, succ)
    return (G, node_hash)


def checkFp(trace_graph, pre, val):
    ctlgraph = {} 
    for key, G in trace_graph.items():
        print(f"------run {key}--------")
        print(f"----nodes: {G.nodes}")
        G.graph['Fp']={"holds":False, "state":None}
        for node in G.nodes:
            values = G.nodes[node]['vars']
            checkp = [i[pre] for i in values]
            print(f"getting {node} node data for checking Fp: {values}")
            print(f"get the predicate values to check: {checkp} \n")
            for item in checkp:
                if int(node) != 1 and item == val:
                    G.graph['Fp']={"holds":True, "state":int(node)}
                    break  
        ctlgraph[key] = G
    return ctlgraph


def checkrAFp(trace_graph, pre, val):
    ctlgraph = {}
    allnodes = list(nx.dfs_preorder_nodes(trace_graph, (1,0,0)))
    for node in allnodes:
        if node[pre] == val:
            nx.set_node_attributes(trace_graph, {node:True}, "p")
        else:
            nx.set_node_attributes(trace_graph, {node:False}, "p")
        print(f"node {node} data: {trace_graph.nodes[node]}")       
    ctlgraph = trace_graph         
    succnodes = list(trace_graph.neighbors((1,0,0)))
    afp = True
    for item in succnodes:
        fp = False
        succnodes = list(nx.dfs_preorder_nodes(trace_graph, item))
        # print(f"depths list nodes for {item} is : {succnodes}")
        for n in succnodes:
            value = ctlgraph.nodes[n]["p"]
            if fp or value:
                fp = True
                break
        afp = afp and fp
    ctlgraph.graph['AFp'] = afp 
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
        
def getrResult(result_graph):
    resutls = {}
    hold = result_graph.graph['AFp']
    cex = (None, None)
    results = {"Holds": hold, "CEX": cex}
    return results        
        

   
def main (program, iter_num, predicate, value):
    #run the program with random number to generate traces
    traces = gettcs(program, iter_num)
    # tracegraph = transi(traces)
    nodehash = {}
    tracegraph, nodehash = transiG(traces, nodehash)
    # print (f"graph from traces: {tracegraph.nodes}")

    resultgraph = checkrAFp(tracegraph, predicate, value)
    results = getrResult(resultgraph)
    print(f"The Property AF(y==0) holds for the input program: {results}")
             
    # drawG(tracegraph)

# we can use a stack to store all the sub formula, pop one by one to check?
    # resultgraph = checkFp(tracegraph, predicate, value)
    # for key, graph in tracegraph.items():
    #     print(f"----run {key} of nodes data:\n {graph.nodes(data=True)} \n")
    #     print(f"----run {key} of results:\n {graph.graph} \n")
    # results = getResult(resultgraph)
    # print(f"The Property AF(y==0) holds for the input program: {results}")
    # drawG(tracegraph)
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

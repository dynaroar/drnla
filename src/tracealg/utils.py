import os, subprocess, re
import shlex, shutil
import networkx as nx
import matplotlib.pyplot as plt

import ltl as L
from z3 import *
from random import randrange, randint, seed


# draw the trace graph, default to 4 subplots
def drawG(graph):
    for key, graph in graph.items():
        if key < 4:
            loc = 221 + int(key)
            plt.subplot(loc)
            # plt.figure()
            nx.draw(graph, with_labels=True, node_size = 20)
            # labels = nx.get_node_attributes(graph, 'vars')
            # nx.draw(graph, labels=labels, font_weight='bold')
    # nx.draw(graph, with_labels=True, node_size = 20)
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
        nondet_input = randint(-50, 50)
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
        subR = initFormulas(sf2, [sf2]+subfs)
        return initFormulas(sf1, [sf1]+subR)
    else:
        raise Exception(f"Not a valid ltl formula {str(phi)}")
    


# test cases to debug
def initTest():
    # aphash = dict()
    # aphash['p'] = 'x<0' # should z3 ast
    # aphash['q'] = 'y==0' # 
    # G(AP(x<0) Or F(AP(y==0))), default the order, <s
    # atomic1 = L.AtomicProposition('p')
    # atomic2 = L.AtomicProposition('q')
    
    atomic1 = L.AtomicProposition(Int('x')<0)
    atomic2 = L.AtomicProposition(Int('y')==0)
    phiF = L.F(atomic2)
    phiOr = L.Or(atomic1, phiF)
    phiG = L.G(phiOr)

    subfs = initFormulas(phiG, [phiG])
    # subfs = [atomic1, atomic2, phiF, phiOr, phiG]
    print(f"subformulae lists: {subfs}")
    return subfs

def test1():
    phi = L.AtomicProposition(Int('x')>=0)
    subfs = initFormulas(phi, [phi])
    print(f"subformulae lists: {subfs}")
    return subfs

def test2():
    phi = L.AtomicProposition(Int('x')>0)
    phiG = L.G(phi)
    subfs = initFormulas(phiG, [phiG])
    print(f"subformulae lists: {subfs}")
    return subfs

def test3():
    phi = L.AtomicProposition(Int('x')>0)
    phiG = L.G(phi)
    phiF = L.F(phiG)
    subfs = initFormulas(phiF, [phiF])
    print(f"subformulae lists: {subfs}")
    return subfs

def test4():
    phi1 = L.AtomicProposition(Int('x')<0)
    phi2 = L.AtomicProposition(Int('y')>=0)
    phiOr = L.Or(phi1, phi2) 
    phiG = L.G(phiOr)
    subfs = initFormulas(phiG, [phiG])
    print(f"subformulae lists: {subfs}")
    return subfs


def test5():
    phi1 = L.AtomicProposition(Int('x')<0)
    phi2 = L.AtomicProposition(Int('y')>=0)
    phiand = L.And(phi1, phi2)
    phiG = L.G(phiand)
    subfs = initFormulas(phiG, [phiG])
    print(f"subformulae lists: {subfs}")
    return subfs


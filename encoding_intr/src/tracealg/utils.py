import os, subprocess, re
import shlex, shutil
import networkx as nx
import matplotlib.pyplot as plt

from random import randrange, randint, seed

vars_name = ['loc', 'x', 'y', 'z', 'a', 'b', 'c']

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
 

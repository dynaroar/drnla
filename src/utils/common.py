import logging
import argparse
import subprocess, shlex
import re

def getLogger(name, level):
    logger = logging.getLogger(name)
    logger.setLevel(logging.DEBUG)
    ch = logging.StreamHandler()
    ch.setLevel(level)
    formatter = logging.Formatter("%(name)s:%(levelname)s:%(message)s")
    ch.setFormatter(formatter)
    logger.addHandler(ch)
    return logger

def getLogLevel(level):
    assert level in set(range(5))
    if level == 0:
        return logging.CRITICAL
    elif level == 1:
        return logging.ERROR
    elif level == 2:
        return logging.WARNING
    elif level == 3:
        return logging.INFO
    else:
        return logging.DEBUG


def runCmd(cmd):
    subprocess.run(shlex.split(cmd), capture_output=True, check=True, text=True)

    # subprocess.run(shlex.split(cmd), check=True, text=True, shell=True)
    
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
    runCmd(compiled_cmd)
    trace_path = f"{progpath}/traces"
    if not os.path.exists(trace_path):
        os.makedirs(trace_path)
    else :
        shutil.rmtree(trace_path)
        os.makedirs(trace_path)

    trace_file = f"{trace_path}/{progname}.tcs"
    fw = open(trace_file, "w")
    # print("vtrace28; I x; I y; I c", file=fw)
 
    for i in range(iter):
        nondet_input = randint(-50, 50)
        # with open(trace_file, 'w+') as f:
        subprocess.call(['./' + progpath +'/'+ progname, str(nondet_input), "0"], stdout=fw)
    # print("vtrace28; I x; I y; I c", file=fw)
    fw.close()
    print("trace generated!")

 

def processInvars(file_invs, file_processed):
    fr = open(file_invs, "r")
    # x = fileInvs.split(".")
    # outInvs = x[0]+"_refine.inv"
    # print(outInvs)
    invsList = []
    for line in fr:
        itermList = re.split(";", line.rstrip('\n'))
        invsList.append(itermList)
    fw = open(file_processed, 'w')
    for traceVars in invsList:
        invars = []
        # invars.append(traceVars[0])
        for inv in traceVars[1:]:
            # print(inv[-1])
            if inv[-1] == "1":
                invars.append(inv[:-1])
        # print(';'.join(invars))
        fw.writelines(traceVars[0]+';'+'&&'.join(invars)+'\n')
    fw.close            
    print (invsList)

def processTrace(fileTrace):
    pass
  
if __name__ == "__main__":
    aparser = argparse.ArgumentParser("Run c program to collect traces.")
    ag = aparser.add_argument
    ag("--inp", "-i", type=str, help="input c program")
    args = aparser.parse_args()
    # main(args.inp, args.n, args.p, args.v)
    processInvars(args.inp)

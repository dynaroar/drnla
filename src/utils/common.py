import logging


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



def init_prog (program):
    pass


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
    

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


def run_cmd(cmd):
    try:
        result = subprocess.run(shlex.split(cmd), check=True, capture_output=True, text=True)
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f'command run failed:\n{e.stderr}')

def vtrace_case(error_case):
    model_case = re.search(r'(\w+)_too_.*_(\d+)', error_case)
    if model_case:
        case, loc = model_case.groups()
        return f'vtrace_{case}_{loc}'
     
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

 
def process_invars(file_invs):
    fr = open(file_invs, "r")
    invs_list = []
    for line in fr:
        invars=[]
        iterms = re.split(";", line.rstrip('\n'))        
        for inv in iterms[1:]:
            if inv[-1] == "1":
                invars.append(inv[:-1].strip())
        invs_list.append((iterms[0].strip(),invars))
    fr.close()
    return invs_list

def init_invars(file_processed, invs_list, nla_ou):
    fw = open(file_processed, 'w')
    for loc_str, invars in invs_list:
        if 'vtrace_if_' in loc_str:
            loc_if = re.findall(r'\d+', loc_str)[0]
            (nla, if_ou, else_ou) = nla_ou[loc_if]
            if_ou = invars
            nla_ou[loc_if] = (nla, if_ou, else_ou)
        if 'vtrace_else_' in loc_str:
            loc_else = re.findall(r'\d+', loc_str)[0]
            (nla, if_ou, else_ou) = nla_ou[loc_else]
            else_ou = invars
            nla_ou[loc_else] = (nla, if_ou, else_ou)
    
    for loc, (nla, if_ou, else_ou) in nla_ou.items():
        loc_if = 'vtrace_if_'+loc
        loc_else = 'vtrace_else_'+loc
        if_ou, else_ou = list(set(if_ou).difference(else_ou)), list(set(else_ou).difference(if_ou))
        nla_ou[loc] = (nla, if_ou, else_ou)
        fw.writelines(loc_if+';'+' && '.join(if_ou)+'\n')
        fw.writelines(loc_else+';'+' && '.join(else_ou)+'\n')
    fw.close()            
  

def process_trace(file_trace):
    pass


def clean():
    cwd = os.path.dirname(__file__)
    items = os.listdir(cwd)
    for item in items:
        if item.endswith(".i") or item.endswith(".o"):
            os.remove(os.path.join(cwd, item))


            
if __name__ == "__main__":
    aparser = argparse.ArgumentParser("Run c program to collect traces.")
    ag = aparser.add_argument
    ag("--inp", "-i", type=str, help="input c program")
    args = aparser.parse_args()
    # main(args.inp, args.n, args.p, args.v)
    processInvars(args.inp)

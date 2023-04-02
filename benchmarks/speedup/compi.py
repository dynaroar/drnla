#!/usr/bin/python3

import os, sys, fileinput, subprocess
import shlex, time, random
#This is a relative path directory

def runCmd(cmd):
    try:
        result = subprocess.run(shlex.split(cmd), check=True, capture_output=True, text=True)
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f'command run failed:---{cmd}---\n{e.stderr}')

def argvReplace(s):
    with open(s, 'r') as file:
        cnt = 0
        lines = file.readlines()
        for i, line in enumerate(lines):
            if "__VERIFIER_nondet_int();" in line:
                cnt += 1
                lines[i] = line.replace("__VERIFIER_nondet_int();", f"argv[{cnt}];")
        with open(s, 'w') as file:
            file.writelines(lines)

def compile():
    bench = sys.argv[1]
    files = [f for f in os.listdir(bench) if os.path.isfile(os.path.join(bench, f))]
    for src in files:
        if src.endswith('.c'):
            cfile = os.path.join(bench, src)
            argvReplace(cfile)
            bin = os.path.join(bench, src.split(".")[0])
            gcc_cmd = f'gcc {cfile} -o {bin}'
            runCmd(gcc_cmd)    
          
def main():
    compile()
 
if __name__ == "__main__":
    main()

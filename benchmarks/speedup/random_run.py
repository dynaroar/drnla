#!/usr/bin/python3

import os, sys, fileinput, subprocess
import shlex, time, random
import statistics
#This is a relative path directory

def runCmd(cmd):
    try:
        result = subprocess.run(shlex.split(cmd), check=True, capture_output=True, text=True)
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f'command run failed:---{cmd}---\n{e.stderr}')

def runTime(cmd):
    # process_time() getting CPU time
    # time() gets Wall time
    start = time.time()
    runCmd(cmd)
    end = time.time()
    return round((end - start), 4)
    # return end - start
  
            
def randRun(nla, lia, args, res, tbnla, tblia, tbspd):
    nla_time = []
    lia_time = []
    for i in range(10):
        inputs = [str(random.randint(-100, 100)) for i in range(args)]
        inputs_str = ' '.join(inputs)
        nla_run = f'./{nla} {inputs_str}'
        lia_run = f'./{lia} {inputs_str}'
        nla_time.append(runTime(nla_run))
        lia_time.append(runTime(lia_run))
    nla_avg = statistics.mean(nla_time)
    lia_avg = statistics.mean(lia_time)
    speedup = round((nla_avg / lia_avg), 4)
    # speedup = nla_avg / lia_avg
    tbnla.append(nla_avg)
    tblia.append(lia_avg)
    tbspd.append(speedup)
    res.write(f'{nla} & {nla_avg} & {lia_avg} & {speedup} \\\\ \n')
    print(f'{nla} & {nla_avg} & {lia_avg} & {speedup} \\')
     
def main():
    
    # nla = sys.argv[1]
    # lia = sys.argv[2]
    # args = int(sys.argv[3])
    # randRun(nla, lia, args)
    res = open('results.tex', 'w')
    res.write(f'Benchmark & Origin(s) & Linear(s) & Speedup \\\\ \n')
    res.write(f'\\hline \n')
  
    with open(sys.argv[1], 'r') as file:
        lines = file.readlines()
        tbnla, tblia, tbspd = [], [], []
    
        for line in lines:
            bins = line.strip().split(' ')
            print(f'----Running benchmark: {bins[0]}-----')
            randRun(bins[0], bins[1], int(bins[2]), res, tbnla, tblia, tbspd)
    res.write(f'\\hline \n')
    nla_over, lia_over, spd_over = statistics.mean(tbnla), statistics.mean(tblia), statistics.mean(tbspd)
    res.write(f' Average & {nla_over} & {lia_over} & {spd_over} \\\\ \n')
    res.write(f'\\hline \n')
  
    res.close()
    print('Results saved to results.tex')
                     
if __name__ == "__main__":
    main()

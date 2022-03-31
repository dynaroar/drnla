import cparser
from z3 import *
from collections import defaultdict
import random

cex = r"""
[L355]              int x ;
[L356]              int y ;
[L357]              int if_too_small_3 ;
[L358]              int else_too_big_3 ;
[L359]              int else_too_small_3 ;
[L360]              int if_too_big_3 ;
[L363]  COND TRUE   y == 10 || x != 5
        VAL         [x=5, y=10]
[L364]  COND FALSE  !(x == 5 && ! (x == 5 && y == 10))
        VAL         [x=5, y=10]
[L368]  COND TRUE   ! (! (x == 5 || (x == 5 && y == 10)))
[L369]              if_too_small_3 = 1
        VAL         [if_too_small_3=1, x=5, y=10]
[L370]              reach_error()
        VAL         [if_too_small_3=1, x=5, y=10]
"""

ult_cex_parser = cparser.UltCexParser()
f = ult_cex_parser.to_z3(cex)
print(f)
s = z3.Solver()
# set_option('smt.arith.random_initial_value', True)
# set_option('smt.random_seed', random.randint(0, 2 ** 8))
cmodels = []
c = 0
x0, y0 = Ints('x0 y0')
mconstr = True
counters = defaultdict(dict)
inp_vars = [x0, y0]
print(f'if_too_small_3; I x; I y')
while c < 1000:
    c += 1
    mf = And(f, mconstr)
    s.push()
    s.add(mf)
    if s.check() == sat:
        m = s.model()
        cmodels.append(m)
        cconstr = True
        for v in inp_vars:
            if m[v] not in counters[str(v)]:
                counters[str(v)][m[v]] = 1
            else:
                counters[str(v)][m[v]] += 1
            if counters[str(v)][m[v]] > 10:
                cconstr = And(cconstr, v != m[v])
            
        mconstr = And(mconstr, Or([z3.Int(v.name()) != m[v] for v in m.decls()]))
        x = m[z3.Int('x0')]
        y = m[z3.Int('y0')]
        print(f'if_too_small_3; {x}; {y}')
        # mconstr = And(mconstr, cconstr)
        s.pop()
        # set_option('smt.random_seed', random.randint(0, 2 ** 8))
    else:
        print(mf)
        s.pop()
        break

# for m in cmodels:
#     x = m[z3.Int('x0')]
#     y = m[z3.Int('y0')]
#     print(f'if_too_big_3; {x}; {y}')

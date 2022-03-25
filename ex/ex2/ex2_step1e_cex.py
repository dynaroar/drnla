import cparser
from z3 import *

cex = r"""
    [L355]             int x ;
    [L356]             int if_too_small_3 ;
    [L357]             int else_too_big_3 ;
    [L358]             int else_too_small_3 ;
    [L359]             int if_too_big_3 ;
    [L362]  COND TRUE  x * x == 49
            VAL        [x=7]
    [L363]  COND TRUE  - x <= 0
    [L364]             else_too_big_3 = 1
            VAL        [else_too_big_3=1, x=7]
    [L365]             reach_error()
            VAL        [else_too_big_3=1, x=7]
    """

ult_cex_parser = cparser.UltCexParser()
f = ult_cex_parser.to_z3(cex)
print(f)
s = z3.Solver()
cmodels = []
c = 0
mconstr = True
while c < 50:
    c += 1
    mf = And(f, mconstr)
    s.push()
    s.add(mf)
    if s.check() == sat:
        m = s.model()
        cmodels.append(m)
        mconstr = And(mconstr, Or([z3.Int(v.name()) != m[v] for v in m.decls()]))
        s.pop()
    else:
        s.pop()
        break

print(cmodels)

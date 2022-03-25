import cparser
from z3 import *

cex = r"""
    [L355]              int x ;
    [L356]              int if_too_small_3 ;
    [L357]              int else_too_big_3 ;
    [L358]              int else_too_small_3 ;
    [L359]              int if_too_big_3 ;
    [L362]  COND FALSE  !(x * x == 49)
            VAL         [x=-8]
    [L373]  COND FALSE  !((x <= 7 && - x <= -7) || x == -7)
            VAL         [x=-8]
    [L377]  COND TRUE   ! (- x <= 0 && x != 7)
    [L378]              else_too_small_3 = 1
            VAL         [else_too_small_3=1, x=-8]
    [L379]              reach_error()
            VAL         [else_too_small_3=1, x=-8]
    """

ult_cex_parser = cparser.UltCexParser()
f = ult_cex_parser.to_z3(cex)
s = z3.Solver()
cmodels = []
c = 0
mconstr = True
print("else_too_small_3; I x")
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

for m in cmodels:
    print(f"else_too_small_3; {m[z3.Int('x0')]}")

# [L355]              int n ;
# [L356]              int x ;
# [L357]              int y ;
# [L358]              int z ;
# [L359]              int k ;
# [L362]              n = 0
# [L363]              x = 0
# [L364]              y = 1
# [L365]              z = 6
#         VAL         [n=0, x=0, y=1, z=6]
# [L366]  COND TRUE   1
#         VAL         [n=0, x=0, y=1, z=6]
# [L367]  COND FALSE  !(((3 * n) * n + 3 * n) + 1 <= k)
#         VAL         [k=0, n=0, x=0, y=1, z=6]
# [L375]  COND FALSE  !(- n <= 0 && - k + y <= 0)
#         VAL         [k=0, n=0, x=0, y=1, z=6]
# [L378]  COND TRUE   ! (- n <= -1 && k - y <= -1)
#         VAL         [k=0, n=0, x=0, y=1, z=6]
# [L379]              reach_error()
#         VAL         [k=0, n=0, x=0, y=1, z=6]

from z3 import *

k0, n0, x0, y0, z0 = Ints('k0 n0 x0 y0 z0')

cex = And(n0 == 0, x0 == 0, y0 == 1, z0 == 6,
          Not(((3 * n0) * n0 + 3 * n0) + 1 <= k0),
          Not(And(- n0 <= 0, - k0 + y0 <= 0)),
          Not(And(- n0 <= -1, k0 - y0 <= -1)))
print(cex)

print("vtrace_else_8; I k; I n; I x; I y; I z")

c = 0
constr = True
s = Solver()
while c < 50:
    f = And(cex, constr)
    s.push()
    s.add(f)
    if s.check() == sat:
        m = s.model()
        s.pop()
        print(f'vtrace_else_8; {m[k0]}; {m[n0]}; {m[x0]}; {m[y0]}; {m[z0]}')
        constr = And(constr, Or(k0 != m[k0], n0 != m[n0], x0 != m[x0], y0 != m[y0], z0 != m[z0]))
        c += 1
    else:
        s.pop()
        break




from z3 import *

k, n, x, y, z = Ints('k n x y z')
fs = [-n <= -1, k - y <= -1]
cs = [x == 0, n == 0, y - 1 == 0, z - 6 == 0, n <= 0, k - x <= 0, -n - x <= 0, -n + x <= 0]
s = Solver()
s.push()
s.add(And(cs))
rs = []
rem = []
for f in fs:
    s.push()
    s.add(Not(f))
    if s.check() != unsat:
        rs.append(f)
    else:
        rem.append(f)
    s.pop()
s.pop()
print(rs)
res = And(rem)
for r in rs:
    s.push()
    s.add(r)
    for c in cs:
        s.push()
        s.add(c)
        if s.check() == unsat:
            res = And(res, Or(r, c))
        s.pop()
    s.pop()
print(simplify(res))
t1 = Tactic('ctx-solver-simplify')
t2 = Tactic('simplify')
t = Then(t2, t1)
g = Goal()
g.add(res)
print(t(g))
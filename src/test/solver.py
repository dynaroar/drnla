from z3 import *

def prove(f):
    s = Solver()
    s.add(Not(f))
    if s.check() == unsat:
        print ("Satisfied!")
    else:
        print("Unsatisfied:")
        print(s.model())


#  z <= 0
# 2. x <= 5
# 3. -x <= 1
# 4. -z <= 20
# 5. x + z <= 2
# 6. -x + z <= -2

x = Int ('x')
z = Int ('z')

# pre0 = (x == (-z*z+2*z+6))
pre1 = (z == (-5*x*x+20*x -20))

# pre1 = (z == If ((-5*x*x+20*x -20) > -20, (-5*x*x+20*x -20), -20))
# iteration 1 pre2 = (x <= 2)
# pre2 = (x <= 3)
#3 pre2 = (x <= 4)
# pre2 = (x <= 6)
# pre2 = (x <= 7)

# satisfied!

# 2. x <= 5
# 3. z <= 0
# 4. -x <= 0


pre2 = And ((x <= 5), (x >= -1), (z>=-20), (z+x)<=2, (x-z)>=2)              

# pre3 = (-x + z ) % 4 == 1 
formula1 = Implies(pre1, pre2)
prove(formula1)

        

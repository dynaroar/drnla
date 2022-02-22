from z3 import *

def prove(f):
    s = Solver()
    s.add(Not(f))
    if s.check() == unsat:
        print ("Satisfied!")
    else:
        print("Unsatisfied:")
        print(s.model())

 
x = Int ('x')
z = Int ('z')

# # pre0 = (x == (-z*z+2*z+6))
# pre1 = (z == (-5*x*x+20*x -20))
# # pre1 = (z == If ((-5*x*x+20*x -20) > -20, (-5*x*x+20*x -20), -20))
# pre2 = And ((x <= 5), (x >= -1), (z>=-20), (z+x)<=2, (x-z)>=2)              
# pre3 = (-x + z ) % 4 == 1 
# formula1 = Implies(pre1, pre2)  

C = (x*x-100) > 0
C1 = x>=11
C2 = And (x>=0, x<=8)

case1 = And(C, C1, C2)
case2 = And(C, C1, Not(C2))
case3 = And(C, Not(C1), C2)
case4 = And(C, Not(C1), Not(C2))
case5 = And(Not(C), C1, C2)
case6 = And(Not(C), C1, Not(C2))
case7 = And(Not(C), Not(C1), C2)
case8 = And(Not(C), Not(C1), Not(C2))
 
cases = [case1,case2,case3,case4,case5,case6,case7,case8]

for case in cases:
    print (case)
    prove(case)

        

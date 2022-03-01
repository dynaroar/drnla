import sys
import inspect

class Formula(object):
    '''
    A class representing LTL formula.
    '''
    __desc__ = 'LTL formula'
    pass


 
class AtomicProposition(Formula):
    '''
    A class representing LTL atomic propositions.

    '''
    
    def __init__(self, atom):
        self.atom = atom

class F(Formula):
    '''
    A class representing LTL F-formulas.

    '''
    symbols = ['F']
 
    def __init__(self, subf):
        self.subformula = subf

class G(Formula):
    '''
    A class representing LTL G-formulas.

    '''
    symbols = ['G']

    def __init__(self, subf):
        self.subformula = subf
  
class Or(Formula):
    '''
    Represents logic non-exclusive disjunction.

    '''
    def __init__(self, formula_left, formula_right):
        self.left = formula_left
        self.right = formula_right
        self.symbols = ['or', '|']


class And(Formula):
    '''
    Represents logic conjunction.

    '''
    def __init__(self, formula_left, formula_right):
        self.left = formula_left
        self.right = formula_right
        self.symbols = ['and', '&']
        

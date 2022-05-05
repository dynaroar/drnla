from lark import Lark, Transformer
from z3 import *
from collections import defaultdict
import operator

class Parser(object):
    pass

class CexParser(Parser):
    pass

ops = {
    '+': operator.add,
    '-': operator.sub,
    '*': operator.mul,
    '/': operator.truediv,
    '%': operator.mod,
    '+=': operator.add,
    '-=': operator.sub,
    '*=': operator.mul,
    '/=': operator.truediv,
    '%=': operator.mod,
    '<': operator.lt,
    '<=': operator.le,
    '>': operator.gt,
    '>=': operator.ge,
    '==': operator.eq,
    '!=': operator.ne }

class UltCexParser(CexParser, Transformer):
    grammar = r"""
        ?cex: stmt+ -> trans_cex

        ?loc: OBRACKET LOC_ID CBRACKET

        ?stmt: 
            | loc instr -> trans_instr
            | loc COND (CTRUE | CFALSE) condition -> trans_cond
            | VAL val_lst -> trans_none

        ?instr: 
            | decl_instr
            | assignment_instr 
            | error_instr

        ?decl_instr: typ ID SEMICOLON -> trans_none

        ?typ: INT_TYP

        ?assignment_instr: 
            | lvar INC -> trans_inc_assign
            | lvar DEC -> trans_dec_assign
            | lvar ASSIGN pexpr -> trans_assign
            | lvar ASSIGN nondet_call -> trans_true
            | lvar ADDEQ pexpr -> trans_op_assign
            | lvar SUBEQ pexpr -> trans_op_assign
            | lvar MULEQ pexpr -> trans_op_assign
            | lvar DIVEQ pexpr -> trans_op_assign
            | lvar MODEQ pexpr -> trans_op_assign

        ?condition: pform

        ?pform: pfdisj

        ?pfdisj: pfconj
            | pfdisj OR pfconj -> trans_disj

        ?pfconj: pfatom
            | pfconj AND pfatom -> trans_conj

        ?pfatom: prel
            | NOT pfatom -> trans_neg
            | OPAREN pform CPAREN -> trans_paren
        
        ?prel: 
            | TRUE -> trans_true
            | FALSE -> trans_false
            | var -> trans_var
            | pexpr EQ pexpr -> trans_binrel
            | pexpr NE pexpr -> trans_binrel
            | pexpr GT pexpr -> trans_binrel
            | pexpr GE pexpr -> trans_binrel
            | pexpr LT pexpr -> trans_binrel
            | pexpr LE pexpr -> trans_binrel
        
        ?pexpr: pterm
            | pexpr ADD pterm -> trans_binop
            | pexpr SUB pterm -> trans_binop
        
        ?pterm: patom
            | pterm MUL patom -> trans_binop
            | pterm DIV patom -> trans_binop
        
        ?patom: num
            | var -> trans_var
            | SUB patom -> trans_uop
            | OPAREN pexpr CPAREN -> trans_paren

        ?nondet_call: (VERIFIER_NONDET | NONDET) OPAREN CPAREN

        ?val_lst: OBRACKET [val (COMMA val)*] CBRACKET

        ?val: var ASSIGN num

        ?var: ID

        ?lvar: ID

        ?num: NUM -> trans_iconst

        ?error_instr: ERROR OPAREN CPAREN -> trans_none

        INT_TYP: "int"
        ASSIGN: "="
        INC: "++"
        DEC: "--"
        ADDEQ: "+="
        SUBEQ: "-="
        MULEQ: "*="
        DIVEQ: "/="
        MODEQ: "%="
        ADD: "+"
        SUB: "-"
        MUL: "*"
        DIV: "/"
        MOD: "%"
        LT: "<"
        LE: "<="
        GT: ">"
        GE: ">="
        EQ: "=="
        NE: "!="
        AND: "&&"
        OR: "||"
        NOT: "!"
        TRUE: "1"
        FALSE: "0"
        CTRUE: "TRUE"
        CFALSE: "FALSE"
        VAL: "VAL"
        COND: "COND"
        COMMA: ","
        SEMICOLON: ";"
        OPAREN: "("
        CPAREN: ")"
        OBRACKET: "["
        CBRACKET: "]"
        LOC_ID: "L" NUM
        ERROR: "reach_error"
        NONDET: "nondet"
        VERIFIER_NONDET: "__VERIFIER_nondet_int"

        %import common.CNAME -> ID
        %import common.SIGNED_NUMBER -> NUM
        %import common.WS
        %ignore WS
        """
    def __init__(self):
        self.sym_tab = {}
        self.ssa_id = defaultdict(int)
    
    def mk_lvar(self, id):
        sid = str(id)
        if sid not in self.ssa_id:
            self.ssa_id[sid] = 0
        else:
            self.ssa_id[sid] += 1
        zid = z3.Int(sid + str(self.ssa_id[sid]))
        self.sym_tab[sid] = zid
        return zid
        
    def mk_var(self, id):
        sid = str(id)
        if sid in self.sym_tab:
            return self.sym_tab[sid]
        else:
            return self.mk_lvar(id)

    def trans_iconst(self, seq):
        (i,) = seq
        return z3.IntVal(i.value)

    def trans_var(self, seq):
        (id,) = seq
        return self.mk_var(id)

    def trans_paren(self, seq):
        (_, e, _) = seq
        return e
    
    def trans_binop(self, seq):
        (el, op, er) = seq
        return ops[op.value](el, er)

    def trans_uop(self, seq):
        (op, e) = seq
        return -e

    def trans_true(self, _):
        return z3.BoolVal(True)

    def trans_false(self, _):
        return z3.BoolVal(False)

    def trans_binrel(self, seq):
        (el, op, er) = seq
        return ops[op.value](el, er)

    def trans_neg(self, seq):
        (_, e) = seq
        return z3.Not(e)

    def trans_conj(self, seq):
        (el, _, er) = seq
        return z3.And(el, er)

    def trans_disj(self, seq):
        (el, _, er) = seq
        return z3.Or(el, er)

    def trans_inc_assign(self, seq):
        (v, _) = seq
        e = self.mk_var(v) + 1
        lv = self.mk_lvar(v)
        return (lv == e)

    def trans_dec_assign(self, seq):
        (v, _) = seq
        e = self.mk_var(v) - 1
        lv = self.mk_lvar(v)
        return (lv == e)

    def trans_assign(self, seq):
        (v, _, e) = seq
        lv = self.mk_lvar(v)
        return (lv == e)

    def trans_op_assign(self, seq):
        (v, op, e) = seq
        ev = self.mk_var(v)
        ne = ops[op](ev, e)
        lv = self.mk_lvar(v)
        return (lv == ne)

    def trans_instr(self, seq):
        (_, i) = seq
        return i

    def trans_cond(self, seq):
        (_, _, _, c) = seq
        return c

    def trans_none(self, _):
        return None

    def trans_stmt(self, seq):
        if len(seq) == 2:
            (_, instr) = seq
        else:
            instr = seq
        return instr

    def trans_cex(self, seq):
        return z3.And([stmt for stmt in seq if stmt is not None])

    parser = Lark(grammar, start="cex")

    def parse(self, s):
        return self.parser.parse(s)

    def to_z3(self, s):
        ast = self.parse(s)
        return self.transform(ast)

# text = r"""
# [L356]              int n ;
# [L357]              int p ;
# [L358]              int q ;
# [L359]              int r ;
# [L360]              int h ;
# [L361]              int c ;
# [L362]              int k ;
# [L363]              int tmp ;
# [L364]              int if_too_small_33 ;
# [L365]              int else_too_big_33 ;
# [L366]              int else_too_small_33 ;
# [L367]              int if_too_big_33 ;
# [L370]              n = __VERIFIER_nondet_int()
# [L371]              p = 0
# [L372]              q = 1
# [L373]              r = n
# [L374]              h = 0
# [L375]              c = 0
# [L376]              tmp = __VERIFIER_nondet_int()
# [L377]              k = tmp
#         VAL         [c=0, h=0, k=-1, n=0, p=0, q=1, r=0, tmp=-1]
# [L378]  COND FALSE  !(q <= n)
#         VAL         [c=0, h=0, k=-1, n=0, p=0, q=1, r=0, tmp=-1]
# [L381]  COND TRUE   1
#         VAL         [c=0, h=0, k=-1, n=0, p=0, q=1, r=0, tmp=-1]
# [L382]  COND FALSE  !((((((((((h * h) * n - ((4 * h) * n) * p) + (4 * (n * n)) * q) - (n * q) * q) - (h * h) * r) + ((4 * h) * p) * r) - ((8 * n) * q) * r) + (q * q) * r) + ((4 * q) * r) * r) + c <= k)
#         VAL         [c=0, h=0, k=-1, n=0, p=0, q=1, r=0, tmp=-1]
# [L393]              if_too_big_33 = 1
#         VAL         [c=0, h=0, if_too_big_33=1, k=-1, n=0, p=0, q=1, r=0, tmp=-1]
# [L394]              reach_error()
#         VAL         [c=0, h=0, if_too_big_33=1, k=-1, n=0, p=0, q=1, r=0, tmp=-1]
# """

# ult_cex_parser = UltCexParser()
# f = ult_cex_parser.to_z3(text)
# print(f)
# s = z3.Solver()
# s.add(f)
# print(s.check())
# print(s.model())

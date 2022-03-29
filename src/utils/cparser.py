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
# [L355]              int n ;
# [L356]              int x ;
# [L357]              int y ;
# [L358]              int z ;
# [L359]              int k ;
# [L360]              int if_too_small_8 ;
# [L361]              int else_too_big_8 ;
# [L362]              int else_too_small_8 ;
# [L363]              int if_too_big_8 ;
# [L367]              n = 0
# [L368]              x = 0
# [L369]              y = 1
# [L370]              z = 6
#         VAL         [k=7, n=0, x=0, y=1, z=6]
# [L371]  COND TRUE   1
#         VAL         [k=7, n=0, x=0, y=1, z=6]
# [L372]  COND TRUE   ((3 * n) * n + 3 * n) + 1 <= k
#         VAL         [k=7, n=0, x=0, y=1, z=6]
# [L373]  COND FALSE  !(y > k - 1)
#         VAL         [k=7, n=0, x=0, y=1, z=6]
# [L377]  COND FALSE  !(! (- k + y <= 0))
#         VAL         [k=7, n=0, x=0, y=1, z=6]
# [L389]              n ++
# [L390]              x += y
# [L391]              y += z
# [L392]              z += 6
#         VAL         [k=7, n=1, x=1, y=7, z=12]
# [L371]  COND TRUE   1
#         VAL         [k=7, n=1, x=1, y=7, z=12]
# [L372]  COND TRUE   ((3 * n) * n + 3 * n) + 1 <= k
#         VAL         [k=7, n=1, x=1, y=7, z=12]
# [L373]  COND TRUE   y > k - 1
# [L374]              else_too_big_8 = 1
#         VAL         [else_too_big_8=1, k=7, n=1, x=1, y=7, z=12]
# [L375]              reach_error()
#         VAL         [else_too_big_8=1, k=7, n=1, x=1, y=7, z=12]
# """

# ult_cex_parser = UltCexParser()
# f = ult_cex_parser.to_z3(text)
# print(f)
# s = z3.Solver()
# s.add(f)
# print(s.check())
# print(s.model())

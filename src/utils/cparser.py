from lark import Lark, Transformer
from z3 import *

class Parser(object):
    pass

class CexParser(Parser):
    pass

class UltCexParser(CexParser, Transformer):
    grammar = r"""
        ?cex: stmt+

        ?stmt: loc? labeled_instr

        ?loc: OBRACKET LOC_ID CBRACKET

        ?labeled_instr: 
            | instr
            | COND (CTRUE | CFALSE) condition
            | VAL val_lst

        ?instr: 
            | decl_instr 
            | assignment_instr 
            | error_instr

        ?decl_instr: typ var SEMICOLON

        ?typ: INT_TYP

        ?assignment_instr: 
            | var INC
            | var DEC
            | var EQ pexpr
            | var ADDEQ pexpr
            | var SUBEQ pexpr
            | var MULEQ pexpr
            | var DIVEQ pexpr
            | var MODEQ pexpr

        ?condition: pform

        ?pform: pfdisj

        ?pfdisj: pfconj
            | pfdisj OR pfconj

        ?pfconj: pfatom
            | pfconj AND pfatom

        ?pfatom: prel
            | NOT pfatom
            | OPAREN pform CPAREN
        
        ?prel: TRUE
            | FALSE
            | var
            | pexpr EQ pexpr
            | pexpr NE pexpr
            | pexpr GT pexpr
            | pexpr GE pexpr
            | pexpr LT pexpr
            | pexpr LE pexpr
        
        ?pexpr: pterm
            | pexpr ADD pterm
            | pexpr SUB pterm
        
        ?pterm: patom
            | pterm MUL patom
            | pterm DIV patom
        
        ?patom: num
            | var
            | SUB patom
            | OPAREN pexpr CPAREN

        ?val_lst: OBRACKET [val (COMMA val)*] CBRACKET

        ?val: var EQ num

        ?var: ID -> mk_var

        ?num: NUM

        ?error_instr: ERROR OPAREN CPAREN

        INT_TYP: "int"
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
        EQ: "="
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
        %import common.INT -> NUM
        %import common.WS
        %ignore WS
        """

    sym_tab = {}

    def mk_var(self, seq):
        (id,) = seq
        if id in self.sym_tab:
            return self.sym_tab[id]
        else:
            zid = z3.Int(id)
            self.sym_tab[id] = zid
            return zid

    parser = Lark(grammar, start="cex")

    def parse(self, s):
        return self.parser.parse(s)

text = r"""
[L355]              int n ;
[L356]              int x ;
[L357]              int y ;
[L358]              int z ;
[L359]              int k ;
[L360]              int if_too_small_8 ;
[L361]              int else_too_big_8 ;
[L362]              int else_too_small_8 ;
[L363]              int if_too_big_8 ;
[L367]              n = 0
[L368]              x = 0
[L369]              y = 1
[L370]              z = 6
        VAL         [k=7, n=0, x=0, y=1, z=6]
[L371]  COND TRUE   1
        VAL         [k=7, n=0, x=0, y=1, z=6]
[L372]  COND TRUE   ((3 * n) * n + 3 * n) + 1 <= k
        VAL         [k=7, n=0, x=0, y=1, z=6]
[L373]  COND FALSE  !(y > k - 1)
        VAL         [k=7, n=0, x=0, y=1, z=6]
[L377]  COND FALSE  !(! (- k + y <= 0))
        VAL         [k=7, n=0, x=0, y=1, z=6]
[L389]              n ++
[L390]              x += y
[L391]              y += z
[L392]              z += 6
        VAL         [k=7, n=1, x=1, y=7, z=12]
[L371]  COND TRUE   1
        VAL         [k=7, n=1, x=1, y=7, z=12]
[L372]  COND TRUE   ((3 * n) * n + 3 * n) + 1 <= k
        VAL         [k=7, n=1, x=1, y=7, z=12]
[L373]  COND TRUE   y > k - 1
[L374]              else_too_big_8 = 1
        VAL         [else_too_big_8=1, k=7, n=1, x=1, y=7, z=12]
[L375]              reach_error()
        VAL         [else_too_big_8=1, k=7, n=1, x=1, y=7, z=12]
"""

ult_cex_parser = UltCexParser()
ast = ult_cex_parser.parse(text)
ult_cex_parser.transform(ast)
print(ast.pretty())
print(ult_cex_parser.sym_tab)

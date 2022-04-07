from z3 import *
from collections import defaultdict
import functools

CONST_TERM_SYM = '#'

class Z3(object):
    @classmethod
    def to_string(cls, f):
        if z3.is_expr(f):
            num_args = f.num_args()
            op = f.decl()
            kop = op.kind()
            if num_args == 0:
                if kop == Z3_OP_TRUE:
                    return str(1)
                elif kop == Z3_OP_FALSE:
                    return str(0)
                elif z3.is_int_value(f): # isinstance(f, IntNumRef):
                    return f.as_string()
                else:
                    return op.name()
            elif num_args == 1:
                if kop == Z3_OP_NOT:
                    sop = '!'
                elif kop == Z3_OP_UMINUS:
                    sop = '-'
                else:
                    sop = op.name()
                return sop + '(' + cls.to_string(f.arg(0)) + ')'
            else:
                if kop == Z3_OP_EQ:
                    sop = '=='
                elif kop == Z3_OP_DISTINCT:
                    sop = '!='
                elif kop == Z3_OP_AND:
                    sop = '&&'
                elif kop == Z3_OP_OR:
                    sop = '||'
                elif kop == Z3_OP_LE:
                    sop = '<='
                elif kop == Z3_OP_GE:
                    sop = '>='
                elif kop == Z3_OP_LT:
                    sop = '<'
                elif kop == Z3_OP_GT:
                    sop = '>'
                elif kop == Z3_OP_ADD:
                    sop = '+'
                elif kop == Z3_OP_SUB:
                    sop = '-'
                elif kop == Z3_OP_MUL:
                    sop = '*'
                elif kop == Z3_OP_DIV or kop == Z3_OP_IDIV:
                    sop = '/'
                else:
                    sop = op.name()
                return '(' + (' ' + sop + ' ').join([cls.to_string(f.arg(i)) for i in range(num_args)]) + ')'
        else:
            raise Exception(f'Unexpected z3 formula: {f}')

    @classmethod
    def split_linear_expr(cls, f):
        terms = defaultdict(int)
        op = f.decl()
        kop = op.kind()
        if z3.is_const(f): # f is constant/variable expression
            if z3.is_int_value(f):
                terms[CONST_TERM_SYM] += f.as_long()
            else:
                terms[op.name()] += 1
        else:
            num_args = f.num_args()
            kop = op.kind()
            if kop == Z3_OP_MUL:
                lhs_arg = f.arg(0)
                rhs_arg = functools.reduce(lambda e1, e2: e1 * e2, [f.arg(i) for i in range(1, num_args)])
                lhs_terms = cls.split_linear_expr(lhs_arg)
                rhs_terms = cls.split_linear_expr(rhs_arg)
                for v1 in lhs_terms:
                    for v2 in rhs_terms:
                        if v1 == CONST_TERM_SYM:
                            if v2 == CONST_TERM_SYM:
                                terms[CONST_TERM_SYM] += lhs_terms[v1] * rhs_terms[v2]
                            else:
                                terms[v2] += lhs_terms[v1] * rhs_terms[v2]
                        else:
                            if v2 == CONST_TERM_SYM:
                                terms[v1] += lhs_terms[v1] * rhs_terms[v2]
                            else:
                                raise Exception(f'Unexpected non-linear term: {f}')
            elif kop == Z3_OP_ADD:
                all_terms = [cls.split_linear_expr(f.arg(i)) for i in range(num_args)]
                for plus_terms in all_terms:
                    for v in plus_terms:
                        terms[v] += plus_terms[v]
            elif kop == Z3_OP_SUB:
                lhs_terms = cls.split_linear_expr(f.arg(0))
                for v in lhs_terms:
                    terms[v] += lhs_terms[v]
                rhs_terms = cls.split_linear_expr(f.arg(1))
                for v in rhs_terms:
                    terms[v] -= rhs_terms[v]
            elif kop == Z3_OP_UMINUS:
                uminus_terms = cls.split_linear_expr(f.arg(0))
                for v in uminus_terms:
                    terms[v] -= uminus_terms[v]
            else:
                raise Exception(f'[split_linear_expr]: Unsupported expression {f}')
        for v in list(terms):
            if terms[v] == 0:
                del terms[v]
        return terms

    @classmethod
    def expr_of_terms(cls, terms):
        term_lst = []
        for v in terms:
            zv = Int(v)
            term_lst.append(terms[v] * zv)
        return functools.reduce(lambda e1, e2: e1 + e2, term_lst)

    @classmethod
    def normalize(cls, f):
        """
        Normalize a condition to the form `e <= const`
        """
        if z3.is_expr(f):
            num_args = f.num_args()
            op = f.decl()
            kop = op.kind()
            if num_args == 2:
                lhs = f.arg(0)
                rhs = f.arg(1)
                if kop == Z3_OP_LE:
                    lhs_terms = cls.split_linear_expr(lhs)
                    rhs_terms = cls.split_linear_expr(rhs)
                    for v in list(rhs_terms):
                        if v != CONST_TERM_SYM:
                            lhs_terms[v] -= rhs_terms[v]
                            del rhs_terms[v]
                            if lhs_terms[v] == 0:
                                del lhs_terms[v]
                    rhs_terms[CONST_TERM_SYM] -= lhs_terms[CONST_TERM_SYM]
                    del lhs_terms[CONST_TERM_SYM]
                    if rhs_terms[CONST_TERM_SYM] == 0:
                        del rhs_terms[CONST_TERM_SYM]
                    return lhs_terms, rhs_terms
                elif kop == Z3_OP_LT:
                    return cls.normalize(lhs <= rhs - 1)
                elif kop == Z3_OP_GE:
                    return cls.normalize(rhs <= lhs)
                elif kop == Z3_OP_GT:
                    return cls.normalize(rhs <= lhs - 1)
                else:
                    return None
            else:
                return None
        else:
            return None

    @classmethod
    def is_same_template(cls, f1, f2):
        norm_f1 = cls.normalize(f1)
        norm_f2 = cls.normalize(f2)
        if norm_f1 and norm_f2:
            f1_lhs_terms, f1_rhs_terms = norm_f1
            f2_lhs_terms, f2_rhs_terms = norm_f2
            for v1 in f1_lhs_terms:
                if v1 not in f2_lhs_terms or f1_lhs_terms[v1] != f2_lhs_terms[v1]:
                    return False
            for v2 in f2_lhs_terms:
                if v2 not in f1_lhs_terms:
                    return False
            return f1_lhs_terms, f1_rhs_terms[CONST_TERM_SYM], f2_rhs_terms[CONST_TERM_SYM]
        else:
            return False

x, y, z = Ints('x y z')
# f = And(x > 0, Or(x < 0, x + y + x >= 0), y < 0)
# print(Z3.to_string(f))
# print(Z3.split_linear_expr(x + y + 2*x + y*2 - x*(2 + 3) + 3 + 2*y*(3 - 1*3)))
template, c1, c2 = Z3.is_same_template(-x + y <= 17, y + x < 2*x + 19)
print(Z3.expr_of_terms(template))
print(c1)
print(c2)
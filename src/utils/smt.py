from z3 import *

class Z3(object):
    @classmethod
    def to_string(cls, f):
        if isinstance(f, z3.ExprRef):
            num_args = f.num_args()
            op = f.decl()
            kop = op.kind()
            if num_args == 0:
                if kop == Z3_OP_TRUE:
                    return str(1)
                elif kop == Z3_OP_FALSE:
                    return str(0)
                elif isinstance(f, IntNumRef):
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

# x, y = Ints('x y')
# f = And(x > 0, Or(x < 0, x + y + x >= 0))
# print(Z3.to_string(f))
from z3 import *
from utils import settings, common
from utils.cparser import*
import ast, operator

# import dynamltl
dynamltl_path = os.path.realpath(os.path.dirname(__file__))
dig_path = os.path.realpath(os.path.join(dynamltl_path, '../deps/dig/src'))
sys.path.insert(0, dig_path)

from helpers.z3utils import Z3
# print(f'----------------system path here(solver): \n {sys.path}')
 
mlog = common.getLogger(__name__, settings.LoggerLevel)

class DynSolver(object):
    vtrace_genf = ''

    def __init__(self, cex):
        self.cex_text = cex
        self.symbols = {}
        self.cex_vars = []
        self.ssa_id = {}
        self.formula = True
        self.error_case = ''
        self.cvars = []
        self.models = []
    
    def parse_to_z3(self):
        cex_parser = UltCexParser()
        cex_z3 = cex_parser.to_z3(self.cex_text)
        self.symbols = cex_parser.sym_tab
        self.cex_vars = [*cex_parser.sym_tab]
        self.ssa_id = cex_parser.ssa_id
        self.formula = cex_z3

    def update_cex(self, cex):
        self.cex_text = cex

    def get_cex_text(self):
        return self.cex_text

    def update_formula(self, f):
        self.formula = f

        

    def gen_model(self):
        c = 0
        constr = True
        s = Solver()
        f=self.formula
        s.add(f)
        models=[]
        while c < 50:
            s.push()
            s.add(constr)
            if s.check() == sat:
                m = s.model()
                models.append(m)
                s.pop()
                or_list = []
                for d in m.decls():
                    or_list.append(Not(z3.Int(d.name()) == m[d]))
                constr = And(constr, Or(or_list))
                c += 1
            else:
                s.pop()
                break
        self.models = models
        # return self.models

    def init_vtrace(self, error_case, vtrace_genf):
        self.error_case = error_case
        vtrace = common.vtrace_case(error_case)
        vnames = self.cex_vars
        mlog.debug(f'------variables from cex_z3 parser: \n {self.cex_vars}')
        for var in vnames:
            if error_case not in var:
                self.cvars.append(var)
       
        decls = list(map(lambda x: f'I {x}', self.cvars))
        decls_str = '; '.join(decls)
        vtrace_decs = f'{vtrace}; {decls_str}\n'
        vtrace_fw = open(vtrace_genf, 'w+')
        mlog.debug(f'------init single vtrace file: \n {vtrace_decs}')
        vtrace_fw.write(vtrace_decs)
        vtrace_fw.close()
        DynSolver.vtrace_genf = vtrace_genf
        
        
    def update_vtrace(self):
        model_list = self.models
        vtrace_fw = open(DynSolver.vtrace_genf, 'a+')
        vtrace = common.vtrace_case(self.error_case)
        for m in model_list:
            vals = list(map(lambda sid: f'{m[self.symbols[sid]]}', self.cvars))
            vals_str = '; '.join(vals)
            vtrace_vals = f'{vtrace}; {vals_str}\n'
            # mlog.debug(f'---vtrace values: \n {vtrace_vals}')
            vtrace_fw.write(vtrace_vals)
        vtrace_fw.close()

    # @classmethod
    # def to_z3(cls, s):
    #     s = s.replace("&&", "and").replace("||", "or").replace("!(", "not(").replace("^", "**").replace('++','+=1').strip()
 
    #     z3f = Z3.parse(s)
    #     return z3f 
 
    @classmethod
    def parse(cls, node):
        """
        Parse sage expr to z3
        e.g., parse(str(sage_expr), use_reals=False)
        Note cannot parse something like tCtr == y - 1/2*sqrt(4*y**2 - 8*x + 4*y + 1) + 1/2
        """
        # print(ast.dump(node))

        if isinstance(node, str):
            node = node.replace("^", "**").replace("&&", "and").replace("||", "or").replace("!(", "not(").replace('++','+=1').strip()


            tnode = ast.parse(node)
            tnode = tnode.body[0].value
            try:
                expr = cls.parse(tnode)
                expr = z3.simplify(expr)
                return expr
            except NotImplementedError:
                mlog.error(f"cannot parse: '{node}'\n{ast.dump(tnode)}")
                raise

        elif isinstance(node, ast.BoolOp):
            vals = [cls.parse(v) for v in node.values]
            op = cls.parse(node.op)
            return op(vals)

        elif isinstance(node, ast.And):
            return z3.And

        elif isinstance(node, ast.Or):
            return z3.Or

        elif isinstance(node, ast.Not):
            return z3.Not

        elif isinstance(node, ast.BinOp):
            left = cls.parse(node.left)
            right = cls.parse(node.right)
            op = cls.parse(node.op)
            return op(left, right)

        elif isinstance(node, ast.UnaryOp):
            operand = cls.parse(node.operand)
            op = cls.parse(node.op)
            return op(operand)

        elif isinstance(node, ast.Compare):
            assert len(node.ops) == 1 and len(
                node.comparators) == 1, ast.dump(node)
            left = cls.parse(node.left)
            right = cls.parse(node.comparators[0])
            op = cls.parse(node.ops[0])
            return op(left, right)

        elif isinstance(node, ast.Name):
            return z3.Int(str(node.id))
        elif isinstance(node, ast.Num):
            return z3.IntVal(str(node.n))
        elif isinstance(node, ast.Add):
            return operator.add
        elif isinstance(node, ast.Mult):
            return operator.mul
        elif isinstance(node, ast.Div):
            return operator.truediv  # tvn:  WARNING: might not be accurate
        elif isinstance(node, ast.FloorDiv):
            return operator.truediv  # tvn:  WARNING: might not be accurate
        elif isinstance(node, ast.Mod):
            return operator.mod
        elif isinstance(node, ast.Pow):
            return operator.pow
        elif isinstance(node, ast.Sub):
            return operator.sub
        elif isinstance(node, ast.USub):
            return operator.neg
        elif isinstance(node, ast.Eq):
            return operator.eq
        elif isinstance(node, ast.NotEq):
            return operator.ne
        elif isinstance(node, ast.Lt):
            return operator.lt
        elif isinstance(node, ast.LtE):
            return operator.le
        elif isinstance(node, ast.Gt):
            return operator.gt
        elif isinstance(node, ast.GtE):
            return operator.ge
 
        else:
            raise NotImplementedError(ast.dump(node))
        

# k0, n0, x0, y0, z0 = Ints('k0 n0 x0 y0 z0')            
# test_f = And(n0 == 0, x0 == 0, y0 == 1, z0 == 6,
#           Not(((3 * n0) * n0 + 3 * n0) + 1 <= k0),
#           Not(And(- n0 <= 0, - k0 + y0 <= 0)),
#           Not(And(- n0 <= -1, k0 - y0 <= -1)))

# dsolver = DynSolver(test_f)
# models = dsolver.gen_model()
# for model in models:
#     print(f'-----each model: \n{model}')
    
#     for x in model.decls():
#         print(f'-----item in each model:{x.name()} = {model[x]}')

invar = "!(x>=0)"
z3f = DynSolver.parse(invar)

print(f'------z3 formula------\n {z3f}')

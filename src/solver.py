from z3 import *
import itertools
from utils import settings, common
from utils.cparser import*
import ast, operator, os, re

dynamltl_path = os.path.realpath(os.path.dirname(__file__))
dig_path = os.path.realpath(os.path.join(dynamltl_path, '../deps/dig/src'))
sys.path.insert(0, dig_path)

from helpers.miscs import Miscs
from data.symstates import SymStates

# from helpers.z3utils import Z3
# print(f'----------------system path here(solver): \n {sys.path}')
 
mlog = common.getLogger(__name__, settings.logger_level)

# class AstRefKey:
#     def __init__(self, n):
#         self.n = n
#     def __hash__(self):
#         return self.n.hash()
#     def __eq__(self, other):
#         return self.n.eq(other.n)
#     def __repr__(self):
#         return str(self.n)
# def askey(n):
#     assert isinstance(n, AstRef)
#     return AstRefKey(n)

def get_vars(f):
    r = set()
    def collect(f):
      if is_const(f): 
          # if f.decl().kind() == Z3_OP_UNINTERPRETED and not askey(f) in r:
          if f.decl().kind() == Z3_OP_UNINTERPRETED and not f in r:
              # r.add(askey(f))
              r.add(f)
      else:
          for c in f.children():
              collect(c)
    collect(f)
    return list(r)

def get_convex(f):
    vars = get_vars(f)
    terms = Miscs.get_terms_fixed_coefs(vars, 2, 1)
    convex_list = []
    for t in terms:
        v, stat = SymStates.mmaximize(f, t, iupper=20)
        if v is not None:
            assert isinstance(v, int), f'{v} is not int type'
            c = t <= v
            convex_list.append(c)
    return convex_list

def and_list(fs):
    if not fs:
        return Not(False)
    elif len(fs) == 1:
        return fs[0]
    else: return And(fs)

def or_list(fs):
    if not fs:
        return Not(False)
    elif len(fs) == 1:
        return fs
    else: return And(fs)

    
class DynSolver(object):
    # vtrace_genf = ''
    # vtrace_cexf = ''

    def __init__(self, cex):
        self.cex_text = cex
        self.symbols = {}
        self.cex_vars = []
        self.ssa_id = {}
        self.zcex = True
        self.error_case = ''
        self.cvars = []
        self.inp_vars = []
        self.models = []
    
    def parse_to_z3(self):
        cex_parser = UltCexParser()
        cex_z3 = cex_parser.to_z3(self.cex_text)
        self.symbols = cex_parser.sym_tab
        self.cex_vars = [*cex_parser.sym_tab]
        self.ssa_id = cex_parser.ssa_id
        self.zcex = cex_z3
    
    def init_cvars(self, error_case):
        self.error_case = error_case
        vnames = self.cex_vars
        # if self.models:
            # vnames = 
        
        mlog.debug(f'------variables from cex_z3 parser/model: \n {self.cex_vars}')
        for var in vnames:
            if error_case not in var:
                self.cvars.append(var)
                self.inp_vars.append(self.symbols[var])

    def update_cex(self, cex):
        self.cex_text = cex

    def get_cex_text(self):
        return self.cex_text

    def update_zcex(self, f):
        self.zcex = f

    def error_zid(self, f):
        pre_pairs = list(map(lambda sid: (z3.Int(sid), self.symbols[sid]), self.cvars))
        mlog.debug(f'substitute mapping: \n {pre_pairs}')
        return (z3.substitute(f, pre_pairs))

        
    def gen_model(self, mconstr):
        mlog.debug(f'gen_model for formula: \n {self.zcex} /\ {mconstr}')
        counters = defaultdict(dict)
        c = 0
        s = Solver()
        models=[]
        while c < settings.snaps:
            c += 1
            mf = And (self.zcex, mconstr)
            s.push()
            s.add(mf)
            result = ''
            if s.check() == sat:
                m = s.model()
                models.append(m)
                cconstr = True
                for v in self.inp_vars:
                    if m[v] not in counters[str(v)]:
                        counters[str(v)][m[v]] = 1
                    else:
                        counters[str(v)][m[v]] += 1
                    if counters[str(v)][m[v]] >= settings.repeat:
                        cconstr = And(cconstr, v != m[v])
                mconstr = And(mconstr, Or([z3.Int(v.name()) != m[v] for v in m.decls()]))
                # mconstr = And(mconstr, cconstr)
                s.pop()
                result = 'sat'
            else:
                mlog.debug(f'unsat:\n {mf}')
                s.pop()
                if c<=1:
                    result = 'unsat'
                else:
                    result = 'sat'
                break
        self.models = models
        if result == 'sat':
            mlog.debug(f'models for generalized: {self.models[0]}')
        return result

  
 
    
        
    def init_vtrace(self, vtrace_file):
        ''' side effect to change both vtrace files of gen and cex
        '''

        vtrace = common.vtrace_case(self.error_case)
        decls = list(map(lambda x: f'I {x}', self.cvars))
        decls_str = '; '.join(decls)
        vtrace_decs = f'{vtrace}; {decls_str}\n'
        vtrace_fw = open(vtrace_file, 'w+')
        # mlog.debug(f'------init single vtrace file: \n {vtrace_decs}')
        vtrace_fw.write(vtrace_decs)
        vtrace_fw.close()
        # DynSolver.vtrace_genf = vtrace_file
        
        
    def write_vtrace_error(self, vtrace_genf):
        model_list = self.models
        vtrace_fw = open(vtrace_genf, 'a+')
        vtrace = common.vtrace_case(self.error_case)
        for m in model_list:
            vals = list(map(lambda sid: f'{m[self.symbols[sid]]}', self.cvars))
            vals_str = '; '.join(vals)
            vtrace_vals = f'{vtrace}; {vals_str}\n'
            # mlog.debug(f'---vtrace values: \n {vtrace_vals}')
            vtrace_fw.write(vtrace_vals)
        vtrace_fw.close()

    def write_vtrace_pre(self, vtrace_cexf):
        model_list = self.models
        vtrace_fw = open(vtrace_cexf, 'a+')
        vtrace = common.vtrace_case(self.error_case)
        cvars0 = list(map(lambda sid: z3.Int(f'{sid}0'), self.cvars))
        
        # mlog.debug(f'----all cvars0 for a cex: \n {model_list} \n {cvars0}')
        for m in model_list:
            vals = list(map(lambda zid0: f'{m[zid0]}', cvars0))
            vals_str = '; '.join(vals)
            vtrace_vals = f'{vtrace}; {vals_str}\n'
            # mlog.debug(f'---vtrace values: \n {vtrace_vals}')
            vtrace_fw.write(vtrace_vals)
        vtrace_fw.close()

    @classmethod
    def not_in(cls, f, f_list):
        defalt = True
        for inv in f_list:
            if cls.is_equal(f, inv):
                return False
        return True

    @classmethod
    def select_or(cls, c_list, i_list):
        c1 = []
        ref_conj = And(i_list)
        mlog.debug(f'i conjunction formula: {ref_conj}')
        for zinv in c_list:
                if cls.is_imply(ref_conj, zinv):
                    c1.append(zinv)
        mlog.debug(f'c1 formula: {c1}')
        c2 = list(set(c_list)-set(c1))
        mlog.debug(f'c2 formula: {c2}')
        r = []
        for c in c2:
            for i in i_list:
                if not cls.is_sat(And(c,i)):
                    r.append(Or(c,i))
        mlog.debug(f'r formula: {r}')
        return c1+r
     
    @classmethod
    def remove_identical (cls, f1_list, f2_list):
        common1 = []
        common2 = []
        for inv1 in f1_list:
            for inv2 in f2_list:
                if cls.is_equal(inv1, inv2):
                    common1.append(inv1)
                    common2.append(inv2)
        return (list(set(f1_list)-set(common1)), list(set(f2_list)-set(common2)))

    @classmethod
    def is_member (cls, fs, f):
        for inv in fs:
            if cls.is_equal(inv, f):
                return True
        return False
    
    @classmethod
    def unsatcore_ou(cls, if_ou, else_ou):
        # foldl = lambda func, acc, xs: reduce(func, xs, acc)
        s = Solver()
        s.set(unsat_core=True)
        s.set(':core.minimize', True)
        i = 0
        j = 0
        if_track = {}
        else_track = {}
        for inv in if_ou:
            i += 1
            p = 'if'+ str(i)
            if_track[p] = inv
            s.assert_and_track(inv, p)
        for inv in else_ou:
            j += 1
            p = 'else'+ str(j)
            else_track[p] = inv
            s.assert_and_track(inv, p)
        if s.check() == 'sat':
            # raise ValueError(f'no unsat core for sat formula:{s.sexpr()}')
            return False
        else:
            unsat_p = s.unsat_core()
            if_unsat = []
            else_unsat = []
            for p in unsat_p:
                p_str = p.sexpr()
                if 'if' in p_str:
                    if_unsat.append(if_track[p_str])
                if 'else' in p_str:
                    else_unsat.append(else_track[p_str])
        return (if_unsat, else_unsat)

    @classmethod
    def rm_weak(cls, f_list):
        sub2 = list(itertools.combinations(f_list, 2))
        rm_f = []
        for (f1, f2) in sub2:
            if DynSolver.is_imply(f1,f2):
                rm_f.append(f2)
            if DynSolver.is_imply(f2,f1):
                rm_f.append(f1)
        if rm_f:
            return cls.rm_weak(list(set(f_list)-set(rm_f)))
        else:
            return f_list

    @classmethod
    def rm_strong(cls, f_list):
        sub2 = list(itertools.combinations(f_list, 2))
        rm_f = []
        for (f1, f2) in sub2:
            if DynSolver.is_imply(f1,f2):
                rm_f.append(f1)
            if DynSolver.is_imply(f2,f1):
                rm_f.append(f2)
        if rm_f:
            return cls.rm_weak(list(set(f_list)-set(rm_f)))
        else:
            return f_list

    @classmethod
    def simp_eqs(cls, f_list):
        g = Goal()
        g.add(f_list)
        t1 = Tactic('simplify')
        t2 = Tactic('solve-eqs')
        t = Then(t1, t2)
        [res] = t(g)
        return res

    @classmethod
    def is_equal(cls, f1, f2):
        s = Solver()
        s.add(Not(f1 == f2))
        r = s.check()
        if r == unsat:
            return True
        else:
            return False
        
    @classmethod
    def is_imply(cls, f1, f2):
        s = Solver()
        s.add(Not(Implies (f1, f2)))
        r = s.check()
        if r == unsat:
            return True
        else:
            return False

    @classmethod
    def is_sat(cls, f):
        s = Solver()
        s.add(f)
        r = s.check()
        if r == sat:
            return True
        else:
            return False
        
    @classmethod
    def parse(cls, node):
        if isinstance(node, str):
            node = node.replace("^", "**").replace("&&", "and").replace("||", "or").replace('++','+=1').strip()
            node = re.sub(r'!(?!=)', 'not', node)


            tnode = ast.parse(node)
            tnode = tnode.body[0].value
            try:
                expr = cls.parse(tnode)
                # expr = z3.simplify(expr)
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
            # print(f'{node.id}: {type(node.id)}')
            return z3.Int(node.id)
        elif isinstance(node, ast.Num):
            return z3.IntVal(node.n)
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
        


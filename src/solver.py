# from helpers.z3utils import Z3
from z3 import *
from utils import settings, common
from utils.cparser import*
import ast, operator

mlog = common.getLogger(__name__, settings.LoggerLevel)

class DynSolver(object):

    def __init__(self, cex):
        cex_parser = UltCexParser()
        cex_z3 = cex_parser.to_z3(cex)
        self.parser = cex_parser
        self.symbols = cex_parser.sym_tab
        self.cex_vars = [*cex_parser.sym_tab]
        self.ssa_id = cex_parser.ssa_id
        self.formula = cex_z3
        self.models = []
             
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
        return self.models
 
    def write_vtrace(self, error_case, vtrace_genf):
        model_list = self.models
        # mlog.debug(f'------writing vtrace file for models: \n {model_list}')
        mlog.debug(f'------variables from cex_z3 parser: \n {self.cex_vars}')
        vnames = self.cex_vars 
        cvars = []
        for var in vnames:
            if error_case not in var:
                cvars.append(var)
       
        decls = list(map(lambda x: f'I {x}', cvars))
        decls_str = '; '.join(decls)
        vtrace_decs = f'{error_case}; {decls_str}\n'
        vtrace_fw = open(vtrace_genf, 'w+')
        mlog.debug(f'---vtrace variables: \n {vtrace_decs}')
        vtrace_fw.write(vtrace_decs)

        for m in model_list:
            vals = list(map(lambda sid: f'{m[self.symbols[sid]]}', cvars))
            vals_str = '; '.join(vals)
            vtrace_vals = f'{error_case}; {vals_str}\n'
            # mlog.debug(f'---vtrace values: \n {vtrace_vals}')
            vtrace_fw.write(vtrace_vals)
        vtrace_fw.close()



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

 

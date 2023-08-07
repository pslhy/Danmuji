import re
import error
import invariant
import sys

# 일단 decl들에서 변수 목록 뽑고
def parse_decl(decl_file):
    declstr = ""
    with open(decl_file, 'r') as f:
        declstr = f.readlines()
    vars = []
    var = {}
    for l in declstr:
        if l.strip().startswith("variable"):
            var["name"] = l.split()[1]
        elif l.strip().startswith("dec-type"):
            if var["name"] == "":
                raise error.ParseException("parse_decl", "Type before variable name")
            var["type"] = l.split()[1]
            vars.append(var)
            var = {}
    return vars

# Trace 파싱해서 되는 값맵, 안되는 값 맵 만들고
def parse_traces(trace_file, decls):
    traceraw = ""
    with open(trace_file, 'r') as f:
        traceraw = f.read()
    tracestrlist = traceraw.split("\n\n..fix_location():::ENTER\n\n\n..fix_location():::EXIT\n")[1:]
    traces = []
    for tracestr in tracestrlist:
        trace = {}
        splittrace = tracestr.split("\n")
        splittrace = list(zip(*[iter(splittrace)]*3))
        for v in splittrace:
            trace[v[0]] = v[1]
        if len(trace.keys()) != len(decls):
            raise error.ParseException("parse_traces", "Trace and decls do not match")
        traces.append(trace)
    return traces

# 그리고 템플릿으로 모든 invariant 만들고
# x < y
# x == y
# var == int_const
# var != int_const
# var >= int_const
# var <= int_const
# x % y == 0
# x - y >= a
# x < c
# var != 0
# ax + by = c
# ax + by < c
# ax + by > c
def generate_invariants(decls, pass_traces, fail_traces):
    invarients = []
    invarients += invariant.infer_IntGreaterThan(decls, pass_traces, fail_traces)
    invarients += invariant.infer_IntEqual(decls, pass_traces, fail_traces)
    invarients += invariant.infer_OneOfScalar(decls, pass_traces, fail_traces)
    invarients += invariant.infer_IntDivide(decls, pass_traces, fail_traces)
    invarients += invariant.infer_IntNonEqual(decls, pass_traces, fail_traces)
    invarients += invariant.infer_NonZero(decls, pass_traces, fail_traces)
    invarients += invariant.infer_LowerBound(decls, pass_traces, fail_traces, interest=10)
    invarients += invariant.infer_UpperBound(decls, pass_traces, fail_traces, interest=10)
    invarients += invariant.infer_IntDiffLowerBound(decls, pass_traces, fail_traces, interest=10)
    invarients += invariant.infer_IntLimitUpperBound(decls, pass_traces, fail_traces)
    # invarients += invariant.infer_LinearBinaryEqual(decls, pass_traces, fail_traces, interest=3)
    # invarients += invariant.infer_LinearBinaryUpperBound(decls, pass_traces, fail_traces, interest_mult=3, interest_const=3)
    # invarients += invariant.infer_LinearBinaryLowerBound(decls, pass_traces, fail_traces, interest_mult=3, interest_const=3)
    return invarients

def is_IntDiffLowerBound(expr):
    pattern = r'^\s*([\w-]+)\s*-\s*([\w-]+)\s*>=\s*(-?\d+)\s*$'
    match = re.match(pattern, expr)
    if match:
        x, y, a = match.groups()
        return x, y, int(a)
    else:
        return None, None, None

def is_IntGreaterThan(expr):
    pattern = r'^\s*([\w-]+)\s*<\s*([\w-]+)\s*$'
    match = re.match(pattern, expr)
    if match:
        x, y = match.groups()
        return x, y
    return None, None

def sanitize_invariants(invariants):
    for invariant in invariants:
        x, y, a = is_IntDiffLowerBound(invariant)
        x2, y2 = is_IntGreaterThan(invariant)
        if x is not None: # 1 * x + -1 * y > a-1 / -1 * x + 1 * y < -a+1 / x - y >= a 
            duplicate_invariant1 = '1 * '+x+' + -1 * '+y+' > '+str(a-1)
            duplicate_invariant2 = '-1 * '+x+' + 1 * '+y+' < '+str(-a+1)
            if duplicate_invariant1 in invariants:
                invariants.remove(duplicate_invariant1)
            if duplicate_invariant2 in invariants:
                invariants.remove(duplicate_invariant2)
        elif ' >= 1' in invariant: # var != 0  / var >= 1
            duplicate_invariant = invariant.replace(' >= 1', ' != 0')
            if duplicate_invariant in invariants:
                invariants.remove(duplicate_invariant)
        elif x2 is not None: # x < y / -1 * x + 1 * y > 0 / 1 * x + -1 * y < 0
            duplicate_invariant1 = '-1 * '+x2+' + 1 * '+y2+' > 0'
            duplicate_invariant2 = '1 * '+x2+' + -1 * '+y2+' < 0'
            if duplicate_invariant1 in invariants:
                invariants.remove(duplicate_invariant1)
            if duplicate_invariant2 in invariants:
                invariants.remove(duplicate_invariant2)
        else:
            pass
    return invariants

# decls = parse_decl("./test/daikon.decls")
# pass_traces = parse_traces("./test/pass.dtrace", decls)
# fail_traces = parse_traces("./test/fail.dtrace", decls)
# invariants = list(set(generate_invariants(decls, pass_traces, fail_traces)))
# print(len(invariants))
# print(sanitize_invariants(invariants))

decls = parse_decl(sys.argv[1])
pass_traces = parse_traces(sys.argv[2], decls)
fail_traces = parse_traces(sys.argv[3], decls)
invariants = list(set(generate_invariants(decls, pass_traces, fail_traces)))
print("\n".join(sanitize_invariants(invariants)))
print(len(sanitize_invariants(invariants)))


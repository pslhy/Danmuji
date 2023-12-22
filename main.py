import re
import error
import invariant
import sys
import argparse
from tqdm import tqdm

STAR_REPLACE = "STARTOKEN"
ARROW_REPLACE = "ARROWTOKEN"
DOT_REPLACE = "DOTTOKEN"

parser = argparse.ArgumentParser(description='Daikon-like invariant generator')
parser.add_argument('decl_file', metavar='decl_file', type=str, help='decl file')
parser.add_argument('pass_trace_file', metavar='pass_trace_file', type=str, help='pass trace file')
parser.add_argument('fail_trace_file', metavar='fail_trace_file', type=str, help='fail trace file')
parser.add_argument('--verbose', dest='verbose', action='store_true', help='verbose mode')
parser.set_defaults(verbose=False)
args = parser.parse_args()


def printv(m):
    if args.verbose:
        print(m)

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
            # var["name"] = l.split()[1].replace("*", STAR_REPLACE).replace("->", ARROW_REPLACE).replace(".", DOT_REPLACE)
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
            trace[v[0]] = int(v[1])
        if len(trace.keys()) != len(decls):
            raise error.ParseException("parse_traces", "Trace and decls do not match")
        traces.append(trace)
    return traces

# var == const
# var != 0
# var >= const
# var > var
# var - var >= const
# (var * var * (var + const) < const) 

def generate_invariants(decls):
    invariants = []
    printv("Generating OneOfScalar")
    invariants += invariant.generate_OneOfScalar(decls)
    printv("Generating NonZero")
    invariants += invariant.generate_NonZero(decls)
    printv("Generating LowerBound")
    invariants += invariant.generate_LowerBound(decls)
    printv("Generating IntGreaterThan")
    invariants += invariant.generate_IntGreaterThan(decls)
    printv("Generating IntDiffLowerBound")
    invariants += invariant.generate_IntDiffLowerBound(decls)
    printv("Generating IntDivUpperBound")
    invariants += invariant.generate_IntDivUpperBound(decls)
    # printv("Generating TripleMultUpperBound")
    # invariants += invariant.generate_TripleMultUpperBound(decls)

    return invariants

def prepare_eval(invariant, trace):
    ptrace = {k.replace("*", STAR_REPLACE).replace("->", ARROW_REPLACE).replace(".", DOT_REPLACE): int(v) for k, v in trace.items()}
    return ptrace


def validate_invariants(pass_traces, fail_traces, invariants):
    def validate_invariant(invariant, traces, is_pass=True):
        eval_as_func = eval('lambda v: ' + invariant)
        for trace in traces:
            if eval_as_func(trace) != is_pass:
                return False
        return True
    
    printv("Validating pass traces")
    looper = invariants
    if args.verbose:
        looper = tqdm(invariants)
    passed_invariants = [inv for inv in looper if validate_invariant(inv,pass_traces)]
    printv("Validating fail traces")
    looper = passed_invariants
    if args.verbose:
        looper = tqdm(passed_invariants)
    result = [inv for inv in looper if validate_invariant(inv,fail_traces, False)]
    result = [res.replace("v[", "").replace("]", "") for res in result]
    return result


decls = parse_decl(args.decl_file)
pass_traces = parse_traces(args.pass_trace_file, decls)
fail_traces = parse_traces(args.fail_trace_file, decls)
invariants = list(set(generate_invariants(decls)))
print("Hypothesis Space :",len(invariants))
printv("Validate invariants")
validated = validate_invariants(pass_traces, fail_traces, invariants)
printv(validated)
print("\n".join(validated))
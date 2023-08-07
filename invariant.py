# x < y
def infer_IntGreaterThan(decls, pass_traces, fail_traces):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for y in decls:
            if y["type"] != "int":
                continue
            if x["name"] == y["name"]:
                continue
            # Check for pass traces (hard constraint)
            passed = True
            for trace in pass_traces:
                if int(trace[x["name"]]) >= int(trace[y["name"]]):
                    passed = False
                    break
            if not passed:
                continue
            # Check for fail traces
            failed = False
            for trace in fail_traces:
                if int(trace[x["name"]]) < int(trace[y["name"]]):
                    failed = True
                    break
            if failed:
                continue
            invariants.append(x["name"] + " < " + y["name"])
    return invariants

# x == y
def infer_IntEqual(decls, pass_traces, fail_traces):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for y in decls:
            if y["type"] != "int":
                continue
            if x["name"] == y["name"]:
                continue
            # Check for pass traces (hard constraint)
            passed = True
            for trace in pass_traces:
                if int(trace[x["name"]]) != int(trace[y["name"]]):
                    passed = False
                    break
            if not passed:
                continue
            # Check for fail traces
            failed = False
            for trace in fail_traces:
                if int(trace[x["name"]]) == int(trace[y["name"]]):
                    failed = True
                    break
            if failed:
                continue
            invariants.append(x["name"] + " == " + y["name"])
    return invariants
        
# var == int_const
def infer_OneOfScalar(decls, pass_traces, fail_traces):
    invariants = []
    for x in decls:
        nums = set([int(trace[x["name"]]) for trace in pass_traces])
        if len(nums) != 1:
            continue
        target_num = nums.pop()
        fail_nums = set([int(trace[x["name"]]) for trace in fail_traces])
        if target_num in fail_nums:
            continue
        invariants.append(x["name"] + " == " + str(target_num))
    return invariants

# var >= int_const
def infer_LowerBound(decls, pass_traces, fail_traces, interest):
    invariants = []
    for x in decls:
        nums = list(set([int(trace[x["name"]]) for trace in pass_traces]))
        if len(nums) < 1:
            continue
        target_num = min(nums)
        for i in range(0, interest):
            # Check for fail traces
            fail_nums = list(set([int(trace[x["name"]]) for trace in fail_traces]))
            if len(fail_nums) > 0 and max(fail_nums) >= (target_num - i):
                continue
            invariants.append(x["name"] + " >= " + str(target_num - i))
    return invariants

# var <= int_const
def infer_UpperBound(decls, pass_traces, fail_traces, interest):
    invariants = []
    for x in decls:
        nums = list(set([int(trace[x["name"]]) for trace in pass_traces]))
        if len(nums) < 1:
            continue
        target_num = max(nums)
        for i in range(0, interest):
            # Check for fail traces
            fail_nums = list(set([int(trace[x["name"]]) for trace in fail_traces]))
            if len(fail_nums) > 0 and min(fail_nums) <= (target_num + i):
                continue
            invariants.append(x["name"] + " <= " + str(target_num + i))
    return invariants

# x % y == 0
def infer_IntDivide(decls, pass_traces, fail_traces):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for y in decls:
            if y["type"] != "int":
                continue
            if x["name"] == y["name"]:
                continue
            # Check for pass traces (hard constraint)
            passed = True
            for trace in pass_traces:
                if int(trace[y["name"]]) == 0:
                    passed = False
                    break
                if int(trace[x["name"]]) % int(trace[y["name"]]) != 0:
                    passed = False
                    break
            if not passed:
                continue
            # Check for fail traces
            failed = False
            for trace in fail_traces:
                if int(trace[y["name"]]) == 0:
                    failed = True
                    break
                if int(trace[x["name"]]) % int(trace[y["name"]]) == 0:
                    failed = True
                    break
            if failed:
                continue
            invariants.append(x["name"] + " % " + y["name"] + " == 0")
    return invariants

# x - y >= a
def infer_IntDiffLowerBound(decls, pass_traces, fail_traces, interest):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for y in decls:
            if y["type"] != "int":
                continue
            if x["name"] == y["name"]:
                continue
            nums = list(set([int(trace[x["name"]]) - int(trace[y["name"]]) for trace in pass_traces]))
            if len(nums) < 1:
                continue
            target_num = min(nums)
            for i in range(0, interest):
                # Check for fail traces
                fail_nums =list(set([int(trace[x["name"]]) - int(trace[y["name"]]) for trace in fail_traces]))
                if len(fail_nums) > 0 and max(fail_nums) >= (target_num - i):
                    continue
                invariants.append(x["name"] + " - " + y["name"] + " >= " + str(target_num - i))
    return invariants

# IntNonEqual
def infer_IntNonEqual(decls, pass_traces, fail_traces):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for y in decls:
            if y["type"] != "int":
                continue
            if x["name"] == y["name"]:
                continue
            # Check for pass traces (hard constraint)
            passed = True
            for trace in pass_traces:
                if int(trace[x["name"]]) == int(trace[y["name"]]):
                    passed = False
                    break
            if not passed:
                continue
            # Check for fail traces
            failed = False
            for trace in fail_traces:
                if int(trace[x["name"]]) != int(trace[y["name"]]):
                    failed = True
                    break
            if failed:
                continue
            invariants.append(x["name"] + " != " + y["name"])
    return invariants

# IntLimitUpperBound
def infer_IntLimitUpperBound(decls, pass_traces, fail_traces):
    limits = [256, 32768, 65536, 1048576, 2147483648, 4294967296]
    invariants = []
    for x in decls:
        nums = list(set([int(trace[x["name"]]) for trace in pass_traces]))
        if len(nums) < 1:
            continue
        target_num = max(nums)
        for limit in limits:
            if target_num < limit:
                # Check for fail traces
                fail_nums = list(set([int(trace[x["name"]]) for trace in fail_traces]))
                if len(fail_nums) > 0 and min(fail_nums) < limit:
                    continue
                invariants.append(x["name"] + " < " + str(limit))
    return invariants

# var != null
def infer_NonZero(decls, pass_traces, fail_traces):
    invariants = []
    for x in decls:
        nums = set([int(trace[x["name"]]) for trace in pass_traces])
        if 0 in nums:
            continue
        fail_nums = set([int(trace[x["name"]]) for trace in fail_traces])
        if fail_nums != set([0]):
            continue
        invariants.append(x["name"] + " != 0")
    return invariants

def is_mutually_prime(a, b):
    while b != 0:
        a, b = b, a % b
    return a == 1

# ax + by = c
def infer_LinearBinaryEqual(decls, pass_traces, fail_traces, interest):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for y in decls:
            if y["type"] != "int":
                continue
            if x["name"] == y["name"]:
                continue
            for a in range(-interest, interest):
                first_value = None
                if a == 0:
                    continue
                for b in range(-interest, interest):
                    if b == 0:
                        continue
                    if not is_mutually_prime(abs(a), abs(b)):
                        continue
                    passed = True
                    first_value = None
                    # Check for pass traces (hard constraint)
                    for trace in pass_traces:
                        if first_value is None:
                            first_value = int(trace[x["name"]]) * a + int(trace[y["name"]]) * b
                        if first_value != int(trace[x["name"]]) * a + int(trace[y["name"]]) * b:
                            passed = False
                            break
                    if not passed:
                        continue
                    # Check for fail traces
                    failed = False
                    for trace in fail_traces:
                        if first_value == int(trace[x["name"]]) * a + int(trace[y["name"]]) * b:
                            failed = True
                            break
                    if failed:
                        continue
                    invariants.append(str(a) + " * " + x["name"] + " + " + str(b) + " * " + y["name"] + " == " + str(first_value))
    return invariants

# ax + by <= c
def infer_LinearBinaryUpperBound(decls, pass_traces, fail_traces, interest_mult, interest_const):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for y in decls:
            if y["type"] != "int":
                continue
            if x["name"] == y["name"]:
                continue
            for a in range(-interest_mult, interest_mult):
                first_value = None
                if a == 0:
                    continue
                for b in range(-interest_mult, interest_mult):
                    if b == 0:
                        continue
                    if not is_mutually_prime(abs(a), abs(b)):
                        continue
                    for c in range(0, interest_const):
                        passed = True
                        first_value = None
                        # Check for pass traces (hard constraint)
                        for trace in pass_traces:
                            if first_value is None:
                                first_value = int(trace[x["name"]]) * a + int(trace[y["name"]]) * b + c
                            if first_value < int(trace[x["name"]]) * a + int(trace[y["name"]]) * b:
                                passed = False
                                break
                        if not passed:
                            continue
                        # Check for fail traces
                        failed = False
                        for trace in fail_traces:
                            if first_value >= int(trace[x["name"]]) * a + int(trace[y["name"]]) * b:
                                failed = True
                                break
                        if failed:
                            continue
                        invariants.append(str(a) + " * " + x["name"] + " + " + str(b) + " * " + y["name"] + " <= " + str(first_value))
    return invariants

# ax + by >= c
def infer_LinearBinaryLowerBound(decls, pass_traces, fail_traces, interest_mult, interest_const):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for y in decls:
            if y["type"] != "int":
                continue
            if x["name"] == y["name"]:
                continue
            for a in range(-interest_mult, interest_mult):
                first_value = None
                if a == 0:
                    continue
                for b in range(-interest_mult, interest_mult):
                    if b == 0:
                        continue
                    if not is_mutually_prime(abs(a), abs(b)):
                        continue
                    for c in range(0, interest_const):
                        passed = True
                        first_value = None
                        # Check for pass traces (hard constraint)
                        for trace in pass_traces:
                            if first_value is None:
                                first_value = int(trace[x["name"]]) * a + int(trace[y["name"]]) * b - c
                            if first_value > int(trace[x["name"]]) * a + int(trace[y["name"]]) * b:
                                passed = False
                                break
                        if not passed:
                            continue
                        # Check for fail traces
                        failed = False
                        for trace in fail_traces:
                            if first_value <= int(trace[x["name"]]) * a + int(trace[y["name"]]) * b:
                                failed = True
                                break
                        if failed:
                            continue
                        invariants.append(str(a) + " * " + x["name"] + " + " + str(b) + " * " + y["name"] + " >= " + str(first_value))
    return invariants
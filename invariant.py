global_specials = [2,4,8,16,32,64,100,128,256,512,1024,2048,4096,8192,16384,32767,65535,1048575,2147483647,4294967295]

# var == const
def generate_OneOfScalar(decls, lower_bound=-10, upper_bound=100, specials=global_specials):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for i in list(set(list(range(lower_bound, upper_bound)) + specials)):
            invariants.append("v['" + x["name"] + "']" + " == " + str(i))
    return invariants
# var != 0
def generate_NonZero(decls):
    invariants = []
    for x in decls:
        invariants.append("v['" + x["name"] + "']" + " != 0")
    return invariants

# var >= const
def generate_LowerBound(decls, lower_bound=-10, upper_bound=10, specials=global_specials):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for i in list(set(list(range(lower_bound, upper_bound)) + specials)):
            invariants.append("v['" + x["name"] + "']" + " >= " + str(i))
    return invariants

# var > var
def generate_IntGreaterThan(decls):
    invariants = []
    for x in decls:
        for y in decls:
            if y["type"] != x["type"]:
                continue
            if x["name"] == y["name"]:
                continue
            invariants.append("v['" + x["name"] + "']" + " > " + "v['" +  y["name"] + "']")
    return invariants

# var - var >= const
def generate_IntDiffLowerBound(decls, lower_bound=1, upper_bound=10, specials=global_specials):
    invariants = []
    for x in decls:
        for y in decls:
            if y["type"] != x["type"]:
                continue
            if x["name"] == y["name"]:
                continue
            for i in list(set(list(range(lower_bound, upper_bound)) + specials)):
                invariants.append("v['" + x["name"] + "']" + " - " + "v['" + y["name"] + "']" + " >= " + str(i))
    return invariants

# var <= var / const
def generate_IntDivUpperBound(decls, lower_bound=2, upper_bound=10):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for y in decls:
            if y["type"] != x["type"]:
                continue
            if x["name"] == y["name"]:
                continue
            for i in range(lower_bound, upper_bound):
                invariants.append("v['" + x["name"] + "']" + " <= " + "v['" + y["name"] + "']" + " / " + str(i))
    return invariants

# (var * var * (var + const1) < const2) 
def generate_TripleMultUpperBound(decls, lower_bound=1, upper_bound=10, specials=global_specials):
    invariants = []
    for x in decls:
        if x["type"] != "int":
            continue # Only int
        for y in decls:
            if y["type"] != x["type"]:
                continue
            if y["type"] != "int":
                continue # Only int
            for z in decls:
                if z["type"] != x["type"]:
                    continue
                if z["type"] != "int":
                    continue
                for c1 in list(set(list(range(lower_bound, upper_bound)) + specials)):
                    for c2 in list(set(list(range(lower_bound, upper_bound)) + specials)):
                        invariants.append(x["name"] + " * " + y["name"] + " * (" + z["name"] + " + " + str(c1) + ") < " + str(c2))
    return invariants
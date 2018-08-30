# function to read a file output by the gp or magma scripts, return
# two dictionaries both with keys (N,k,nchar), one with valies
# dimension-list, the other with times.

from sage.all import ZZ, QQ, PolynomialRing, pari, copy, NumberField

def read_dims(fname):
    dims_dict = {}
    times_dict = {}
    max_time = tot_time = tot_time0 = 0.0
    max_space = None
    nspaces = 0
    nspaces0 = 0 # exclude trvial spaces
    for L in open(fname).readlines():
        N,k,chi,t,dims = L.split(":")
        N=int(N)
        k=int(k)
        chi=int(chi)
        t=float(t)
        # the -2 below is because the dims string ends "]\n"
        dims = [] if  dims=="[]\n" else [int(d) for d in dims[1:-2].split(",")]
        key = (N,k,chi)
        if key in dims_dict:
            print("Duplicate data for {}".format(key))
        dims_dict[key] = dims
        times_dict[key] = t
        if t>max_time:
            max_time = t
            max_space = key
        tot_time += t
        nspaces += 1
        if dims:
            nspaces0 += 1
            tot_time0 += t
    print("Read {} spaces of which {} are nontrivial.  Total cpu time = {}s".format(nspaces, nspaces0, tot_time))
    print("Max time = {} for space {}".format(max_time, max_space))
    print("Average time (all spaces)      = {}".format(tot_time/nspaces))
    print("Average time (nonzero spaces)  = {}".format(tot_time0/nspaces0))
    return dims_dict, times_dict

def read_polys(fname):
    polys_dict = {}
    nspaces = 0
    nspaces0 = 0 # exclude trvial spaces
    for L in open(fname).readlines():
        N,k,chi,dims,polys = L.split(":")
        N=int(N)
        k=int(k)
        chi=int(chi)
        # the -2 below is because the string ends "\n"
        polys = eval(polys.replace("\n",""))
        dims2 = [p if p in ZZ else len(p)-1 for p in polys]
        dims=eval(dims)
        dims=[d for d in dims if d<=20]
        if dims!=dims2:
            print("dims from file = {}".format(dims))
            print("dims from coeffs = {}".format(dims2))
            return

        key = (N,k,chi)
        if key in polys_dict:
            print("Duplicate data for {}".format(key))
        polys.sort()
        polys_dict[key] = polys
        nspaces += 1
        if polys:
            nspaces0 += 1
    print("Read {} spaces of which {} are nontrivial.".format(nspaces, nspaces0))
    return polys_dict

def str_intlist_to_intlist(s):
    if s=="[]":
        return []
    return [int(i) for i in s[1:-1].split(",")]

def str_intlistlist_to_intlistlist(s):
    if s=="[]":
        return []
    return [[int(i) for i in si.split(",")] for si in s[2:-2].split("],[")]

def str_intlistlistlist_to_intlistlistlist(s):
    if s=="[]":
        return []
    return eval(s)

def read_dtp(fname):
    # read full data: N:k:i:t:dims:traces:polys:junk
    data = {}
    max_time = tot_time = tot_time0 = 0.0
    max_space = None
    nspaces = 0
    nspaces0 = 0 # exclude trvial spaces
    for L in open(fname).readlines():
        fields = L.split(":")
        N=int(fields[0])
        k=int(fields[1])
        chi=int(fields[2])
        key = (N,k,chi)
        if key in data:
            print("Duplicate data for {}".format(key))
        t=float(fields[3])
        if t>max_time:
            max_time = t
            max_space = key
        tot_time += t
        dims =   str_intlist_to_intlist(fields[4])
        traces = str_intlistlist_to_intlistlist(fields[5])
        polys =  str_intlistlist_to_intlistlist(fields[6])
        # NB field 7 only holds data in magma output, field 8 only in gp output
        coeffs =  str_intlistlistlist_to_intlistlistlist(fields[8]) if len(fields)>=9 else []

        data[key] = {'dims':dims, 'traces':traces, 'polys':polys, 'coeffs':coeffs}
        nspaces += 1
        if polys:
            nspaces0 += 1
    print("Read {} spaces of which {} are nontrivial.".format(nspaces, nspaces0))
    print("Max time = {} for space {}".format(max_time, max_space))
    print("Average time (all spaces)      = {}".format(tot_time/nspaces))
    print("Average time (nonzero spaces)  = {}".format(tot_time0/nspaces0))
    return data

def bdd_dims(dims_dict, dmax=20):
    # given a dims_dict return a smaller dict of only those (N,k,chi)
    # with a dim<=dmax
    res = {}
    for key in dims_dict.keys():
        dims = dims_dict[key]
        if any(d<=dmax for d in dims):
            res[key] = dims
    return res

def sagepol(paripol, var='x'):
    Qx = PolynomialRing(QQ,var)
    return Qx(str(paripol))

def polredabs(pol):
    x = pol.parent().variable_name()
    return sagepol(pari(pol).polredabs(),x)

def compare_data(d1,d2, keylist=['dims', 'traces', 'polys']):
    assert d1.keys()==d1.keys()
    QX = PolynomialRing(QQ,'x')
    for k in d1.keys():
        if d1[k]!=d2[k]:
            for key in keylist:
                # take copies! we want to be able to change these without affecting the input dicts
                t1=copy(d1[k][key])
                t2=copy(d2[k][key])
                if key=='polys':
                    n=len(t1)
                    for i in range(n):
                        if t1[i]!=t2[i]:
                            pol1 = QX(t1[i])
                            pol2 = QX(t2[i])
                            F1 = NumberField(pol1,'a')
                            F2 = NumberField(pol2,'a')
                            if F1.is_isomorphic(F2):
                                pol1=pol2=F1.optimized_representation()[0].defining_polynomial()
                                t1[i]=t2[i]=list(pol1)

                if t1!=t2:
                    if key=='traces':
                        print("{} differ for {}: \nfirst #= {}, \nsecond #={}".format(key,k,[len(t) for t in t1],[len(t) for t in t2]))
                    else:
                        print("{} differ for {}: \nfirst  {}, \nsecond {}".format(key,k,t1,t2))

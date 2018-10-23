# function to read a file output by the gp or magma scripts, return
# two dictionaries both with keys (N,k,nchar), one with valies
# dimension-list, the other with times.

from sage.all import ZZ, QQ, PolynomialRing, pari, copy, NumberField

def str_intlist_to_intlist(s):
    if s=="[]":
        return []
    return [int(i) for i in s[1:-1].split(",")]

def str_intlistlist_to_intlistlist(s):
    if s=="[]":
        return []
    return [[int(i) for i in si.split(",")] for si in s[2:-2].split("],[")]

def str_nested_list_to_nested_list(s, level=1, T=ZZ, closed=True):
    s=s.replace(" ","")
    if s=="[]":
        return []
    if level==1:
        if closed:
            s=s[1:-1]
        return [T(a) for a in s.split(",")]
    if closed:
        s=s[level:-level]
    delim = "]"*(level-1) + "," + "["*(level-1)
    return [str_nested_list_to_nested_list(a,level-1,T,False)  for a in s.split(delim)]

def decode_ALs(s):
    # input is a string representing a list of list of pairs <p,eps>
    if s=='[]':
        return []
    if s=='[[]]':
        return []
    return str_nested_list_to_nested_list(s.replace("<","[").replace(">","]"),3)

def decode_eigdata(s, key):
    # input is a string representing a list of <pol,bas,n,m,e> where
    # pol is a list of ints, bas is a list of lists of rationals, n &
    # m are ints, and e is a list of lists of lists of ints, i.e.
    # < intlist, ratlistlist, int, int, intlistlist>

    s=s.replace(" ","")
    #print(s)
    if s=='[]':
        return []
    parts = s[2:-2].split(">,<")
    # now each part is a single intlist, ratlistlist, int, int, intlistlist with no "<"...">"
    def decode_one(part):
        pol, rest = part[1:-2].split("],[[")
        #print("pol part is {}".format(pol))
        pol = [ZZ(c) for c in pol.split(",")]
        #print("pol = {}".format(pol))
        bas, rest = rest.split("]],")
        #print("bas part is {}".format(bas))
        bas = [[QQ(str(c)) for c in b.split(",")] for b in bas.split("],[")]
        #print("bas = {}".format(bas))
        #print("Now rest is = {}".format(rest))
        mn, rest = rest.split(",[[")
        #print("mn part is {}".format(mn))
        m,n = [ZZ(c) for c in mn.split(",")]
        #print("m,n ={}".format(m,n))
        #print("Now rest is = {}".format(rest))
        ans = rest.split("],[")
        try:
            ans = [[ZZ(c) for c in an.split(",")] for an in ans]
        except TypeError:
            raise RuntimeError("invalid eigdata for {}: an coefficients not integral: {}".format(key,s))
            #print("ans = {}".format(ans))
        return {'poly':pol, 'basis':bas, 'n':n, 'm':m, 'ans':ans}

    return [decode_one(part) for part in parts]


    # NB We must be careful since eval('1/2') gives 0. so the following cheat does not work!

    #s=s.replace(" ","").replace("<","[").replace(">","]")
    # s = eval(s)
    # return [{'poly':si[0], 'basis':si[1], 'n':si[2], 'm':si[3], 'ans':si[4]} for si in s]

def read_dtp(fname):
    # read full data: N:k:i:t:dims:traces:ALs:polys:cutters:eigdata:cm:it:pra
    data = {}
    max_time = tot_time = tot_time0 = 0.0
    max_space = None
    nspaces = 0
    nspaces0 = 0 # exclude trvial spaces
    norbits = 0
    n20 = 0
    alldims = []
    for L in open(fname).readlines():
        L=L.replace("\n","")
        fields = L.split(":")
        #print(fields)
        N=int(fields[0])
        k=int(fields[1])
        chi=int(fields[2])
        key = (N,k,chi)
        #print(key)
        if key in data:
            print("Duplicate data for {}".format(key))
        t=float(fields[3])
        if t>max_time:
            max_time = t
            max_space = key
        tot_time += t
        dims =   str_nested_list_to_nested_list(fields[4])
        traces = str_nested_list_to_nested_list(fields[5],2)
        ALs = decode_ALs(fields[6])
        polys =  str_nested_list_to_nested_list(fields[7],2)
        eigdata = decode_eigdata(fields[9], key)

        data[key] = {'dims':dims, 'traces':traces, 'ALs': ALs, 'polys':polys, 'eigdata':eigdata}
        nspaces += 1
        norbits += len(dims)
        n20 += sum(0<d<=20 for d in dims)
        if dims:
            nspaces0 += 1
            alldims += dims
            tot_time0 += t
    alldims=list(set(alldims))
    alldims.sort()
    print("Read {} spaces of which {} are nontrivial; {} Galois orbits.".format(nspaces, nspaces0, norbits))
    print("{} orbits have dimension <=20".format(n20))
    print("largest three dimensions: {}".format(alldims[-3:]))
    print("Total time = {:0.3f}".format(tot_time))
    print("Max time = {:0.3f} for space {}".format(max_time, max_space))
    print("Average time (all spaces)      = {:0.3f}".format(tot_time/nspaces))
    print("Average time (nonzero spaces)  = {:0.3f}".format(tot_time0/nspaces0))
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

def polredbest(pol):
    x = pol.parent().variable_name()
    return sagepol(pari(pol).polredbest(),x)

def polredbest_stable(pol):
    x = pol.parent().variable_name()
    f = pari(pol)
    oldf = None
    while f!=oldf:
        oldf, f = f, f.polredbest()
    return sagepol(f,x)

def compare_eigdata(k, ed1, ed2, debug=1):
    #if k==(90,2,12): debug=1
    if debug: print("Comparing eigdata for space {}".format(k))
    if debug>1: print("Comparing eigdata\n1: {}\n2: {}".format(ed1,ed2))
    Qx = PolynomialRing(QQ,'x')
    pol1 = Qx(ed1['poly'])
    pol2 = Qx(ed2['poly'])
    F1 = NumberField(pol1,'a1')
    F2 = F1 if pol1==pol2 else NumberField(pol2,'a2')
    if not F1.is_isomorphic(F2):
        print("poly 1 is {}".format(ed1['poly']))
        print("poly 2 is {}".format(ed2['poly']))
        return False, 'fields not isomorphic'
    if debug:
        print("Field 1 = {}".format(F1))
        print("Field 2 = {}".format(F2))
    #isos = F1.embeddings(F2)
    flag, isos = F1.is_isomorphic(F2,isomorphism_maps=True) # we need to consider all isomorphisms
    if not flag:
        return False, "non-isomorphic Hecke fields"
    isos = [F1.hom([Qx(iso)(F2.gen())]) for iso in isos]
    if debug:
        print("isomorphisms F1 --> F2: {}".format(isos))
        print("Basis matrix 1: {}".format(ed1['basis']))
        print("Basis matrix 2: {}".format(ed2['basis']))
    #d = F1.degree()
    #b1 = [[ed1['basis'][i][j] for j in range(d)] for i in range(d)]
    #basis1 = [F1(co) for co in b1]
    basis1 = [F1(co) for co in ed1['basis']]
    basis2 = [F2(co) for co in ed2['basis']]
    if debug:
        print("Basis 1 = {}".format(basis1))
        print("Basis 2 = {}".format(basis2))
    ans1 = [sum(b*a for a,b in zip(an,basis1)) for an in ed1['ans']]
    ans2 = [sum(b*a for a,b in zip(an,basis2)) for an in ed2['ans']]
    if debug:
        print("ans 1 = {}".format(ans1[:10]))
        print("ans 2 = {}".format(ans2[:10]))

    # now see if there's an isomorphism F1 --> F2 mapping one list to the other:
    for iso in isos:
        if debug:
            print("Trying isomorphism {}".format(iso))
        if all(iso(an1)==an2 for an1,an2 in zip(ans1,ans2)):
            return True, 'match'
    return False, "isomorphic fields but an do not match up"

def compare_data(d1,d2, keylist=['dims', 'traces', 'polys','ALs', 'eigdata'], verbose=False):
    assert d1.keys()==d1.keys()
    QX = PolynomialRing(QQ,'x')
    nforms = len(d1.keys())
    nstep = ZZ(max(1,int(nforms/20.0)))
    nf = 0
    print("Comparing data for {} newforms".format(nforms))
    for k in d1.keys():
        nf+=1
        if nf%nstep==0:
            print("compared {}/{} ({:0.3f}%)".format(nf,nforms,100.0*nf/nforms))
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
                        print("traces differ for {}: \nfirst #= {}, \nsecond #={}".format(k,[len(t) for t in t1],[len(t) for t in t2]))
                        print("first starts\t {}".format(t1[0][:10]))
                        print("second starts\t {}".format(t2[0][:10]))
                    elif key=='eigdata':
                        for f1,f2 in zip(t1,t2):
                            ok, reason = compare_eigdata(k,f1,f2,verbose)
                            if not ok:
                                print("an do not match for (N,k,o)={}: {}".format(k, reason))
                    else:
                        print("{} differ for {}: \nfirst  {}, \nsecond {}".format(key,k,t1,t2))

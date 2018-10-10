from char import DirichletCharacterGaloisReps, NChars
from mf_compare import polredbest_stable#, polredbest, polredabs

from dirichlet_conrey import DirichletCharacter_conrey as DC
from sage.interfaces.gp import Gp
from sage.all import ZZ,QQ, Rational,RR, PolynomialRing, cyclotomic_polynomial, euler_phi, NumberField, primes, Matrix, BackslashOperator
import sys
import time

# This function includes all the intergace to gp, returning a list of
# newforms each of which is a Sage (python) dict containing no gp
# objects.

Qt = PolynomialRing(QQ,'t')
#t = Qt.gen()

def gp2sage_tpol(f):
    # f is a gp object representing an element of QQ[t]
    g = Qt([c.sage() for c in f.Vecrev()])
    return g

def gp2sage_tpolmod(a, Qchi):
    # f is a gp t_ POLMOD object representing an element of QQ[t]/(chipol)
    #print("Converting {} to an element of {}".format(a,Qchi))
    coords = gp2sage_tpol(a.lift()).list()
    d = Qchi.degree()
    coords += [ZZ(0) for _ in range(d-len(coords))]
    b = Qchi(coords)
    #print("...returning {}".format(b))
    return b

def gp2sage_ypoly(f, Qchi_y):
    #f is a gp object representing a polynomial in y with coefficients t_POLMODs (or rationals)
    # Qchi_y is Q(chi)[y]
    Qchi = Qchi_y.base_ring()
    return Qchi_y([gp2sage_tpolmod(a,Qchi) for a in f.Vecrev()])

def gp2sage_rnfelt(an, rnf):
    #an is a polmod in y with coefficients which are polmods in t
    #print("\nconverting {} to {}".format(an,rnf))
    #print("\nconverting {}".format(an))
    sys.stdout.write("converting one an...")
    sys.stdout.flush()
    # This works but is slower (evaluating a polynomial at the generator):
    #return gp2sage_ypoly(an.lift(),rnf.defining_polynomial().parent())(rnf.gen())
    Qchi = rnf.base_field()
    d = rnf.relative_degree()
    coords = [gp2sage_tpolmod(a,Qchi) for a in an.lift().Vecrev()]
    coords += [0 for _ in range(d-len(coords))]
    sys.stdout.write("done\n")
    return rnf(coords)

def gp2sage_rnfelt_list(an, rnf):
    #an is a gp list of polmods in y with coefficients which are polmods in t
    #print("\nconverting {} to {}".format(an,rnf))
    #print("\nconverting {}".format(an))
    sys.stdout.write("converting a list of ans...")
    sys.stdout.flush()
    Qchi = rnf.base_field()
    d = rnf.relative_degree()
    coords = [[gp2sage_tpolmod(c,Qchi) for c in a.lift().Vecrev()] for a in an]
    for c in coords:
        c += [0 for _ in range(d-len(c))]
    sys.stdout.write("have coords, constructing field elements...\n")
    sys.stdout.flush()
    res = [rnf(cc) for cc in coords]
    sys.stdout.write("done\n")
    return res

def gp2sage_anfelt(an, iso):
    # an is a polmod in y with coefficients which are polmods in t, so
    # is a gp object holding an element of a relative number field.
    # iso is an isomorphism from the relative extension to the absolute field.
    # We return the associated element of the absolute field.
    #sys.stdout.write("\nconverting {}...".format(an))
    sys.stdout.write("converting one an...")
    sys.stdout.flush()
    rnf = iso.domain()
    z = iso(rnf.base_field().gen())
    zpow = [z**i for i in range(rnf.base_field().degree())]
    sys.stdout.write("\n# of z powers = {}".format(len(zpow)))
    y = iso(rnf.gen())
    ypow = [y**i for i in range(rnf.relative_degree())]
    sys.stdout.write("\n# of y powers = {}".format(len(ypow)))
    v = [a.lift().Vecrev().sage() for a in an.lift().Vecrev()]
    sys.stdout.write("\nv= (length {})\n".format(len(v)))
    for vi in v: sys.stdout.write("[{}] {}\n".format(len(vi),vi))
    a = sum([sum([ci*zpow[i] for i,ci in enumerate(vj)],0) * ypow[j] for j,vj in enumerate(v)],0)
    sys.stdout.write("\ndone\n")
    sys.stdout.flush()
    return a

def gp2sage_anfelt_list(an, iso):
    # an is a gp list of polmods in y with coefficients which are polmods in t, so
    # each is a gp object holding an element of a relative number field.
    # We return the associated element of the absolute field.
    #sys.stdout.write("\nconverting {}...".format(an))
    #sys.stdout.write("converting one an list...")
    #sys.stdout.flush()
    rnf = iso.domain()
    z = iso(rnf.base_field().gen())
    zpow = [z**i for i in range(rnf.base_field().degree())]
    #sys.stdout.write("\n# of z powers = {}".format(len(zpow)))
    y = iso(rnf.gen())
    ypow = [y**i for i in range(rnf.relative_degree())]
    #sys.stdout.write("\n# of y powers = {}".format(len(ypow)))
    zero = iso.codomain()(0)
    if len(ypow)==1: # Hecke field=Q(chi)
        def convert_one(a):
            #sys.stdout.write("\nconverting {}...".format(a))
            v = a.lift().Vecrev().sage()
            #sys.stdout.write("\nv= (length {})\n".format(len(v)))
            assert len(v)<=len(zpow)
            return  sum([ci*zpow[i] for i,ci in enumerate(v)],zero)
    else:
        def convert_one(a):
            #sys.stdout.write("\nconverting {}...".format(a))
            v = [c.lift().Vecrev().sage() for c in a.lift().Vecrev()]
            #sys.stdout.write("\nv= (length {})\n".format(len(v)))
            assert len(v)<=len(ypow)
            for vi in v:
                #sys.stdout.write("[{}] {}\n".format(len(vi),vi))
                assert len(vi)<=len(zpow)
            return  sum([sum([ci*zpow[i] for i,ci in enumerate(vj)],zero) * ypow[j] for j,vj in enumerate(v)],zero)
    return [convert_one(a) for a in an]


def abstrace(x,deg):
    # absolute trace of a gp int / polmod / polmod pver polmod
    # trace of a t_POLMOD does what is expected but trace of an int
    # doubles it.  Also we might see an int as one coefficient of a newform
    # most of whose coefficients are t_POLMODs.  In this case we need to
    # multiply by the appropriate degree, so have to pass the degree as a
    # parameter.
    #print("abstrace({}) in degree {}".format(x,deg))
    if deg==1:
        #print("---returns(1) {}".format(x.sage()))
        return x.sage()
    if x in QQ: # miraculously this works for a GpElement
        #print("---returns(2) {}".format(deg*QQ(x)))
        return deg*Rational(x)
    try:
        #print("---returns(3) {}".format(x.trace().sage()))
        return x.trace().sage()
    except NameError:
        return x.trace().trace().sage()

def NewSpace(N, k, chi_number,Detail=0):
    Chars = DirichletCharacterGaloisReps(N)
    if chi_number<1 or chi_number>len(Chars):
        print("Character number {} out of range for N={} (should be between 1 and {})".format(chi_number,N,len(Chars)))
        return None
    gp = Gp() # A new gp interface for each space
    gp.default('parisizemax',64000000000)
    G = gp.znstar(N,1)
    chi_sage = Chars[chi_number-1]
    chi_gp = gp.znconreylog(G,DC.number(chi_sage))
    NK = [N,k,[G,chi_gp]]
    return gp.mfinit(NK,0)

# First working version, later repalced by more efficient version:

def oldNewforms(N, k, chi_number, dmax=20, nan=100, Detail=0):
    # N and k are Sage ints but chi is a gp vector
    Chars = DirichletCharacterGaloisReps(N)
    if chi_number<1 or chi_number>len(Chars):
        print("Character number {} out of range for N={} (should be between 1 and {})".format(chi_number,N,len(Chars)))
        return []
    if Detail:
        print("Decomposing space {}:{}:{}".format(N,k,chi_number))
    gp = Gp() # A new gp interface for each space
    gp.default('parisizemax',64000000000)
    G = gp.znstar(N,1)
    chi_sage = Chars[chi_number-1]
    chi_gp = gp.znconreylog(G,DC.number(chi_sage))
    Snew = gp.mfinit([N,k,[G,chi_gp]],0)
    chi_order = DC.multiplicative_order(chi_sage)
    newforms = gp.mfeigenbasis(Snew)
    nnf = len(newforms)
    if nnf==0:
        if Detail:
            print("The space {}:{}:{} is empty".format(N,k,chi_number))
        return []
    if Detail:
        print("The space {}:{}:{} has {} newforms".format(N,k,chi_number,nnf))

    # Setting the character field and polynomial

    # The following line works now but it seems fragile to reply on the internal structure this way.
    #chipoly = Qt(str(newforms[1][1][2][3][4]))
    # Instead we compute the cyclotomic polynomial ourselves, noting
    # that if the character order is 2*m with m odd then Pari uses the
    # m'th cyclotomic polynomial and not the 2m'th (e.g. for a
    # character of order 6 it uses t^2+t+1 and not t^2-t+1).
    chi_order_2 = chi_order//2 if chi_order%4==2 else chi_order
    chipoly = cyclotomic_polynomial(chi_order_2,'t')
    chi_degree = chipoly.degree()
    assert chi_degree==euler_phi(chi_order)==euler_phi(chi_order_2)
    if Detail>1:
        print("chipoly = {}".format(chipoly))

    Qchi = NumberField(chipoly,'z')
    if Detail>1:
        print("Q(chi) = {}".format(Qchi))

    # Setting the polynomials.  These are polynomials in y with coefficients either integers or polmods with modulus chipoly

    Qchi_y = PolynomialRing(Qchi,'y')
    if Detail>1:
        print("Q(chi)[y] = {}".format(Qchi_y))
    pols = gp.mfsplit(Snew,0,1)
    pols = [gp2sage_ypoly(f, Qchi_y) for f in pols[2]]
    dims = [chi_degree*f.degree() for f in pols]
    if dmax==0:
        dmax = max(dims)
    nnf0 = len([d for d in dims if d<=dmax])

    if Detail:
        print("dims = {}, so {} newforms have dimensions <={}".format(dims,nnf0,dmax))
        if Detail>1:
            print("pols = {}".format(pols))

    #Setting the Hecke fields as relative extensions of Qchi and as absolute fields:

    Hecke_fields_relative  = [Qchi.extension(f,'b') for f in pols[:nnf0]]
    abs_polys = [F.absolute_polynomial() for F in Hecke_fields_relative]
    if Detail>1:
        print("absolute pols = {}".format(abs_polys))
    Hecke_fields_absolute = [F.absolute_field('a') for F in Hecke_fields_relative]
    isoms = [F.structure()[1] for F in Hecke_fields_absolute]

    # if Detail:
    #     print("Relative  Hecke fields: {}".format(Hecke_fields_relative))
    #     print("Absolute Hecke fields: {}".format(Hecke_fields_absolute))

    # Compute an's and convert to elements of the (relative) Hecke field:

    coeffs = gp.mfcoefs(Snew,nan)
    ans = [coeffs*gp.mftobasis(Snew,nf) for nf in newforms]
    if Detail>2: print("ans = {}".format(ans))
    # Alternative method for traces:
    traces = [[abstrace(a,d) for a in ansi][1:] for ansi,d in zip(ans,dims)]
    # fix up trace(a_1)
    for i,tr in enumerate(traces):
        tr[0]=dims[i]
    if Detail>2: print("traces = {}".format(traces))

    if Detail>1: print("about to convert ans...")
    ans = [gp2sage_anfelt_list(ansi, iso) for ansi, iso in zip(ans[:nnf0], isoms)]
    if Detail>1: print("finished")
    if Detail>2: print("ans = {}".format(ans))

    # apply polredbest_stable to these polys:
    best_polys = [polredbest_stable(f) for f in abs_polys]
    if Detail>1:
        print("polredbest pols = {}".format(best_polys))
    Hecke_fields = [NumberField(f,'a') for f in best_polys]
    isoms2 = [F1.embeddings(F2)[0] for F1,F2 in zip(Hecke_fields_absolute, Hecke_fields)]

    # adjust all the ans: NB we do not omit a_0 so far for convenience so a_p has index p
    ans = [[iso(an) for an in ansi] for ansi,iso in zip(ans,isoms2)]
    if Detail>2: print("best ans = {}".format(ans))

    if Detail:
        print("Computing Hecke orders...")
    ancs = [[] for _ in range(nnf0)]
    bases = [[] for _ in range(nnf0)]
    for i in range(nnf0):
        if Detail:
            print("#{}:".format(i+1))
        F = Hecke_fields[i]
        ansi = ans[i]
        if dims[i]==1:
            if Detail: print("Hecke field is Q, skipping")
            ancs[i] = [[an] for an in ansi[1:]]
            bases[i] = [[1]]
        else:
            z = F(isoms2[i](isoms[i](Qchi.gen())))
            Fgen = F.gen()
            Ogens = [z,Fgen]
            O = O0 = F.order(Ogens)
            #O = O0 = F.maximal_order()
            D = ZZ(O0.discriminant())
            if Detail:
                print("Hecke field (degree {}) equation order has discriminant {} = {}".format(dims[i],D,D.factor(proof=False)))
            maxp = 1
            for p in primes(2,nan):
                if D.is_squarefree():
                    break
                ap = ansi[p]
                if ap in O:
                    continue
                print("a_{} ={} has coordinates {}".format(p,ap,O.coordinates(ap)))
                maxp = p
                Ogens += [ap]
                print("adding a_{} ={} to order generators".format(p,ap))
                O = F.order(Ogens)
                D = ZZ(O.discriminant())
                if Detail:
                    print("Order now has discriminant {}".format(D))
            if Detail>-1:
                print("Using a_p for p up to {}, order discriminant = {}".format(maxp,D))
            ind = O0.index_in(O)
            bases[i] = [b.list() for b in O.basis()]
            ancs[i] = [O.coordinates(an).list() for an in ansi[1:]]
            # Check that the coordinates and basis are consistent with the original an's:
            for c,b in zip(bases[i],O.basis()):
                assert b==F(c)
            for j in range(nan):
                an = ans[i][j+1]
                bn = sum(c*b for c,b in zip(ancs[i][j],O.basis()))
                if an!=bn:
                    print("**** inconsistent representations of a_{}: value = {} but coordinates give {}".format(j+1,an,bn))
                elif j==1:
                    print("a_2 = {}".format(an))
                    print("coordinates: {}".format(ancs[i][j]))
                    print("basis: {}".format(O.basis()))
                    print("combination of basis = {}".format(bn))
                    print("basis matrix = {}".format(bases[i]))
                    newbasis = [F(co) for co in bases[i]]
                    print("basis from its matrix: {}".format(newbasis))
                    assert O.basis()==newbasis
            if Detail>1:
                print("Hecke order has discriminant {}, contains equation order with index {}\nIntegral basis: {}".format(D, ind, O.basis()))
                print("order basis matrix: {}".format(bases[i]))
                if Detail>2:
                    print("Coefficient vectors of ans: {}".format(ancs[i]))
            if not all(all(anc in ZZ for anc in an) for an in ancs[i]):
                print("*****************************************")
                print("Not all coefficients are integral!")
                print("*****************************************")

    # Compute AL-eigenvalues if character is trivial:
    if chi_order==1:
        Qlist = [(p,p**e) for p,e in ZZ(N).factor()]
        ALs = [gp.mfatkineigenvalues(Snew,Q[1]).sage() for Q in Qlist]
        if Detail: print("ALs: {}".format(ALs))
        # "transpose" this list of lists:
        ALeigs = [[[Q[0],ALs[i][j][0]] for i,Q in enumerate(Qlist)] for j in range(nnf)]
        if Detail: print("ALeigs: {}".format(ALeigs))
    else:
        ALeigs = [[] for _ in range(nnf)]

    all_nf = [
        {'dim': dims[i],
         'chipoly': chipoly,
         'poly': pols[i] if i<nnf0 else None,
         'abs_poly': abs_polys[i] if i<nnf0 else None,
         'best_poly': best_polys[i] if i<nnf0 else None,
         'traces': traces[i],
         'basis': bases[i] if i<nnf0 else None,
         'ans': ans[i] if i<nnf0 else None,
         'ancs': ancs[i] if i<nnf0 else None,
         'ALeigs': ALeigs[i],
        }   for i in range(nnf)]

    if nnf>1:
        all_nf.sort(key=lambda f: f['traces'])
    return all_nf

def Newforms(N, k, chi_number, dmax=20, nan=100, Detail=0):
    t0=time.time()
    Chars = DirichletCharacterGaloisReps(N)
    if chi_number<1 or chi_number>len(Chars):
        print("Character number {} out of range for N={} (should be between 1 and {})".format(chi_number,N,len(Chars)))
        return []
    if Detail:
        print("Decomposing space {}:{}:{}".format(N,k,chi_number))
    gp = Gp() # A new gp interface for each space
    gp.default('parisizemax',64000000000)
    G = gp.znstar(N,1)
    chi_sage = Chars[chi_number-1]
    chi_gp = gp.znconreylog(G,DC.number(chi_sage))
    NK = [N,k,[G,chi_gp]]
    if Detail>1:
        print("NK = {} (gp character = {})".format(NK,chi_gp))
    SturmBound = gp.mfsturm(NK).sage()
    Snew = gp.mfinit(NK,0)
    total_dim = Snew.mfdim()
    # Get the character polynomial

    # Note that if the character order is 2*m with m odd then Pari uses the
    # m'th cyclotomic polynomial and not the 2m'th (e.g. for a
    # character of order 6 it uses t^2+t+1 and not t^2-t+1).

    chi_order = DC.multiplicative_order(chi_sage)
    chi_order_2 = chi_order//2 if chi_order%4==2 else chi_order
    chipoly = cyclotomic_polynomial(chi_order_2,'t')
    chi_degree = chipoly.degree()
    assert chi_degree==euler_phi(chi_order)==euler_phi(chi_order_2)
    if Detail:
        print("Computed newspace {}:{}:{}, dimension={}*{}={}, now splitting into irreducible subspaces".format(N,k,chi_number, chi_degree,total_dim,chi_degree*total_dim))
        if Detail>1:
            print("Sturm bound = {}".format(SturmBound))
            print("character order = {}".format(chi_order))

    # Get the relative polynomials:  these are polynomials in y with coefficients either integers or polmods with modulus chipoly

    pols = gp.mfsplit(Snew,0,1)[2]
    if Detail>2: print("pols[GP] = {}".format(pols))
    nnf = len(pols)
    dims = [chi_degree*gp.poldegree(f) for f in pols]
    if nnf==0:
        if Detail:
            print("The space {}:{}:{} is empty".format(N,k,chi_number))
        gp.quit()
        return []
    if Detail:
        print("The space {}:{}:{} has {} newforms, dimensions {}".format(N,k,chi_number,nnf,dims))

    # Get the traces.  NB (1) mftraceform will only give the trace
    # form on the whole space so we only use this when nnf==1,
    # i.e. the space is irreducible.  Otherwise we'll need to compute
    # traces from the ans.  (2) these are only traces down to Q(chi)
    # so when that has degree>1 (and only then) we need to take an
    # additional trace.
    traces = [None for _ in range(nnf)]
    if nnf==1:
        d = ZZ(chi_degree * gp.poldegree(pols[1]))
        if Detail:
            print("Only one newform so use traceform to get traces")
        traces = gp.mfcoefs(gp.mftraceform(NK), nan)
        if Detail>1:
            print("raw traces: {}".format(traces))
        if chi_degree>1:
            # This is faster than the more simple
            # traces = [c.trace() for c in traces]
            gptrace = gp.eval('c->if(type(c)=="t_POLMOD",trace(c),c*{})'.format(chi_degree))
            traces = gp.apply(gptrace,traces)
            if Detail>1:
                print("traces to QQ: {}".format(traces))
        traces = traces.sage()[1:]
        traces[0] = d
        if Detail>1:
            print("final traces: {}".format(traces))
        traces = [traces]

    # Get the coefficients an.  We'll need these for a newform f if
    # either (1) its dimension is >1 and <= dmax, when we want to
    # store them, or (2) there is more than one newform, so we can
    # later compute the traces from them.  So we don't need them if
    # nnf==1 and the dimension>dmax.


    if nnf>1 or (chi_degree*gp.poldegree(pols[1]))<=dmax:
        if Detail>1:
            print("...computing mfeigenbasis...")
        newforms = gp.mfeigenbasis(Snew)
        if Detail>1:
            print("...computing {} mfcoefs...".format(nan))
        coeffs = gp.mfcoefs(Snew,nan)
        ans = [coeffs*gp.mftobasis(Snew,nf) for nf in newforms]
        if Detail>2:
            print("ans[GP] = {}".format(ans))
    else:
        # there is only one newform (so we have the traces) and its
        # dimension is >dmax (so we will not need the a_n):
        ans = [None for _ in range(nnf)]
        newforms = [None for _ in range(nnf+1)]

    # Compute AL-eigenvalues if character is trivial:
    if chi_order==1:
        Qlist = [(p,p**e) for p,e in ZZ(N).factor()]
        ALs = [gp.mfatkineigenvalues(Snew,Q[1]).sage() for Q in Qlist]
        if Detail: print("ALs: {}".format(ALs))
        # "transpose" this list of lists:
        ALeigs = [[[Q[0],ALs[i][j][0]] for i,Q in enumerate(Qlist)] for j in range(nnf)]
        if Detail: print("ALeigs: {}".format(ALeigs))
    else:
        ALeigs = [[] for _ in range(nnf)]

    Nko = (N,k,chi_number)
    # print("len(traces) = {}".format(len(traces)))
    # print("len(newforms) = {}".format(len(newforms)))
    # print("len(pols) = {}".format(len(pols)))
    # print("len(ans) = {}".format(len(ans)))
    # print("len(ALeigs) = {}".format(len(ALeigs)))

    GP_nfs = [
        { 'Nko': Nko,
          'SB': SturmBound,
          'chipoly': chipoly,
          'GP_newform': newforms[i+1],
          'poly': pols[i+1],
          'ans': ans[i],
          'ALeigs': ALeigs[i],
          'traces': traces[i],
        }   for i in range(nnf)]

    # We could return these as they are but the next processing step
    # will fail if the underlying gp process has quit, so we do the
    # processing here.

    # This processing returns full data but the polynomials have not
    # yet been polredbested and the an coefficients have not been
    # optimized (or even made integral):
    #return GP_nfs

    t1=time.time()
    if Detail:
        print("{}: finished constructing GP newforms (time {:0.3f})".format(Nko,t1-t0))
    nfs = [process_GP_nf(gp, nf, dmax, Detail) for nf in GP_nfs]
    if len(nfs)>1:
        nfs.sort(key=lambda f: f['traces'])
    t2=time.time()
    if Detail:
        print("{}: finished first processing of newforms (time {:0.3f})".format(Nko,t2-t1))
        if Detail>2:
            for nf in nfs:
                if 'eigdata' in nf:
                    print(nf['eigdata']['ancs'])
    nfs = [bestify_newform(nf,dmax,Detail) for nf in nfs]
    t3=time.time()
    if Detail:
        print("{}: finished bestifying newforms (time {:0.3f})".format(Nko,t3-t2))
        if Detail>2:
            for nf in nfs:
                if 'eigdata' in nf:
                    print(nf['eigdata']['ancs'])
    nfs = [integralify_newform(nf,dmax,Detail) for nf in nfs]
    t4=time.time()
    if Detail:
        print("{}: finished integralifying newforms (time {:0.3f})".format(Nko,t4-t3))
        if Detail>2:
            for nf in nfs:
                if 'eigdata' in nf:
                    print(nf['eigdata']['ancs'])
        print("Total time for space {}: {:0.3f})".format(Nko,t4-t0))
    gp.quit()
    return nfs

def NewformTraces(N, k, chi_number, dmax=20, nan=100, Detail=0):
    t0=time.time()
    Chars = DirichletCharacterGaloisReps(N)
    if chi_number<1 or chi_number>len(Chars):
        print("Character number {} out of range for N={} (should be between 1 and {})".format(chi_number,N,len(Chars)))
        return []
    if Detail:
        print("Decomposing space {}:{}:{}".format(N,k,chi_number))
    gp = Gp() # A new gp interface for each space
    gp.default('parisizemax',64000000000)
    G = gp.znstar(N,1)
    chi_sage = Chars[chi_number-1]
    chi_gp = gp.znconreylog(G,DC.number(chi_sage))
    NK = [N,k,[G,chi_gp]]
    if Detail>1:
        print("NK = {} (gp character = {})".format(NK,chi_gp))
    SturmBound = gp.mfsturm(NK).sage()
    Snew = gp.mfinit(NK,0)
    total_dim = Snew.mfdim() # this is the relative dimension i.e. degree over Q(chi)
    # Get the character polynomial

    # Note that if the character order is 2*m with m odd then Pari uses the
    # m'th cyclotomic polynomial and not the 2m'th (e.g. for a
    # character of order 6 it uses t^2+t+1 and not t^2-t+1).

    chi_order = DC.multiplicative_order(chi_sage)
    chi_order_2 = chi_order//2 if chi_order%4==2 else chi_order
    chipoly = cyclotomic_polynomial(chi_order_2,'t')
    chi_degree = chipoly.degree()
    assert chi_degree==euler_phi(chi_order)==euler_phi(chi_order_2)
    if Detail:
        print("Computed newspace {}:{}:{}, dimension={}*{}={}, now splitting into irreducible subspaces".format(N,k,chi_number, chi_degree,total_dim,chi_degree*total_dim))
        if Detail>1:
            print("Sturm bound = {}".format(SturmBound))
            print("character order = {}".format(chi_order))

    if total_dim==0:
        if Detail:
            print("The space {}:{}:{} is empty".format(N,k,chi_number))
        gp.quit()
        return []

    # First just compute Hecke matrices one at a time, to find a splitting operator
    def Hecke_op_iter():
        p=ZZ(1)
        while True:
            p = p.next_prime()
            # while p.divides(N):
            #     p=p.next_prime()
            print("Computing T_{}".format(p))
            yield p, gp.mfheckemat(Snew,p)

    Tp_iter = Hecke_op_iter()
    p, op = Tp_iter.next()
    s1=time.time()
    if Detail:
        print("testing T_{}".format(p))
    f = op.charpoly()
    ok = f.issquarefree()
    if ok and Detail:
        print("Lucky first time: semisimple")
    ops=[(p,op)]
    while not ok:
        pi, opi = Tp_iter.next()
        if Detail:
            print("testing T_{}".format(pi))
        f = opi.charpoly()
        ok = f.issquarefree()
        if ok:
            op = opi
            if Detail:
                print("success using T_{}".format(pi))
            break
        else:
            #ops.append((pi,opi))
            ops += [(pi,opi)]
            if Detail:
                print("T_{} not semisimple".format(pi))
                print("testing combinations...")
            for j in range(5):
                co = [ZZ.random_element(-5,5) for _ in ops]
                while not co:
                    co = [ZZ.random_element(-5,5) for _ in ops]

                if Detail:
                    print("Testing lin comb of {} ops with coeffs {}".format(len(co),co))
                op = sum([ci*opi[1] for ci,opi in zip(co,ops)])
                f=op.charpoly()
                ok = f.issquarefree()
                if ok:
                    if Detail:
                        print("success using {}-combo of T_p for p in {}".format(co,[opi[0] for opi in ops]))
                    break

    if not ok:
        raise RuntimeError("failed to find a 0,1-combination of Tp which is semisimple")
    ffac = f.factor()
    nnf = ffac.matsize()[1]
    gp_pols = ffac.mattranspose()[1,] # syntax [,1] not allowed
    pols = [pol for pol in gp_pols]
    reldims = [pol.poldegree().sage() for pol in pols]
    dims = [d*chi_degree for d in reldims]
    # We'll need the coefficients an, if any newforms have dimension >1 and <=dmax.
    an_needed = [i for i,d in enumerate(dims) if d>1 and d<=dmax]
    if Detail:
        print("Need to compute a_n for {} newforms: {}".format(len(an_needed), an_needed))

    s2=time.time()
    if Detail:
        print("Computed splitting in {:0.3f}, # newforms = {}".format(s2-s1,nnf))
        print("relative dims = {},  absolute dims = {}".format(reldims,dims))

    # Compute AL-matrices if character is trivial:
    if chi_order==1:
        Qlist = [(pr,pr**e) for pr,e in ZZ(N).factor()]
        ALs = [gp.mfatkininit(Snew,Q[1])[2] for Q in Qlist]
        if Detail:
            print("AL-matrices:")
            for Q,AL in zip(Qlist,ALs):
                print("W_{}={}".format(Q[1],AL) )

    if nnf==1 and dims[0]>dmax:
        if Detail:
            print("Only one newform and dim={}, so use traceform to get traces".format(dims[0]))
        traces = gp.mfcoefs(gp.mftraceform(NK), nan)
        if Detail>1:
            print("raw traces: {}".format(traces))
        if chi_degree>1:
            # This is faster than the more simple
            # traces = [c.trace() for c in traces]
            gptrace = gp.eval('c->if(type(c)=="t_POLMOD",trace(c),c*{})'.format(chi_degree))
            traces = gp.apply(gptrace,traces)
            if Detail>1:
                print("traces to QQ: {}".format(traces))
        traces = traces.sage()[1:]
        traces[0] = dims[0]
        if Detail>1:
            print("final traces: {}".format(traces))
        traces = [traces]
    else:  # >1 newform, or just one but its absolute dim is <=dmax
        hs = [f/fi for fi in pols]
        if Detail>1:
            print("fs: {}".format(pols))
            print("hs: {}".format(hs))
            print("  with degrees {}".format([h.poldegree() for h in hs]))
        if Detail>1:
            print("Starting to compute gcds")
        As = [(hi*(fi.gcdext(hi)[2])).subst(gp("x"),op) for fi,hi in zip(pols,hs)]
        if Detail:
            print("Computed idempotent matrix decomposition")
        ims = [A.matimage() for A in As]
        U = gp.matconcat(ims)
        Uinv = U**(-1) # gp("{}^(-1)".format(U.name()))
        if Detail:
            print("Computed U and U^-1")
        starts = [1+sum(d for d in reldims[:i]) for i in range(len(reldims))]
        stops = [sum(d for d in reldims[:i+1]) for i in range(len(reldims))]
        ums = [gp("{}[{}..{},]".format(Uinv.name(),r1,r2)) for r1,r2 in zip(starts,stops)]
        imums = [imA*umA for imA,umA in zip(ims,ums)]
        s3=time.time()
        if Detail:
            print("Computed projectors in {:0.3f}".format(s3-s2))
            print("Starting to compute {} Hecke matrices T_n".format(nan))
        heckemats = gp.mfheckemat(Snew,gp(range(1,nan+1)))
        s4=time.time()
        if Detail:
            print("Computed {} Hecke matrices in {:0.3f}s".format(nan,s4-s3))

        # If we are going to compute any a_n then we now compute
        # umA*T*imA for all Hecke matrices T, whose traces give the
        # traces and whose first columns (or any row or column) give
        # the coefficients of the a_n with respect to some
        # Q(chi)-basis for the Hecke field.

        # But if we only need the traces then it is faster to
        # precompute imA*umA=imAumA and then the traces are
        # trace(imAumA*T).   NB trace(UMV)=trace(VUM)!

        if Detail:
            print("Computing traces")
        # Note that computing the trace of a matrix product is faster
        # than first computing the product and then the trace:
        trpr = gp("(M1,M2) -> [m,n]=matsize(M1); sum(i=1,m,sum(j=1,n,M1[i,j]*M2[j,i]))")
        chitraces = [gp("[{}(m,{}) | m <- {}]".format(trpr.name(),imumA.name(),heckemats.name())) for imumA in imums]
        s4=time.time()
        if Detail:
            print("Computed traces to Q(chi) in {:0.3f}".format(s4-s3))
        gptrace = gp.eval('c->if(type(c)=="t_POLMOD",trace(c),c*{})'.format(chi_degree))
        traces = [gp.apply(gptrace,chitracesA) for chitracesA in chitraces]
        traces = [tracesA.sage() for tracesA in traces]
        s5=time.time()
        if Detail:
            print("Computed traces to Z in {:0.3f}".format(s5-s4))
            for tr in traces:
                print(tr[:20])

    ans = [None for _ in range(nnf)]
    bases = [None for _ in range(nnf)]
    if an_needed:
        if Detail:
            print("...computing a_n...")
        for i in an_needed:
            dr = reldims[i]
            if Detail:
                print("newform #{}/{}, relative dimension {}".format(i,nnf,dr))

            # method: for each irreducible component we have matrices
            # um and im (sizes dr x n and n x dr where n is the
            # relative dimension of the whole space) such that for
            # each Hecke matrix T, its restriction to the component is
            # um*T*im.  To get the eigenvalue in a suitable basis all
            # we need do is take any one column (or row): we choose
            # the first column.  So the computation can be done as
            # um*(T*im[,1]) (NB the placing of parentheses).

            ans[i] = gp("[{}*(m*({}[,1])) | m <- {}]".format(ums[i].name(),ims[i].name(),heckemats.name()))
            if Detail:
                print("ans done")
                if Detail>1:
                    print("an: {}...".format(ans[i]))

            # Now compute the bases (of the relative Hecke field over
            # Q(chi) w.r.t which these coefficients are given.  Here
            # we use e1 because we picked the first column just now.

            B = ums[i]*op*ims[i]
            e1 = gp("{}~".format([int(j==0) for j in range(dr)]))
            cols = [e1]
            while len(cols)<dr:
                cols.append(B*cols[-1])
            W = gp.matconcat(cols)
            bases[i] = W.mattranspose()**(-1)
            if Detail>1:
                print("basis = {}".format(bases[i].lift()))

    # Compute AL-eigenvalues if character is trivial:
    if chi_order==1:
        ALeigs = [[
            [Q[0],gp("({}*({}*({}[,1])))[1]".format(umA.name(),AL.name(),imA.name())).sage()] for Q,AL in zip(Qlist,ALs)]
                  for umA,imA in zip(ums,ims)]
        if Detail: print("ALeigs: {}".format(ALeigs))
    else:
        ALeigs = [[] for _ in range(nnf)]

    Nko = (N,k,chi_number)
    #print("len(traces) = {}".format(len(traces)))
    #print("len(newforms) = {}".format(len(newforms)))
    #print("len(pols) = {}".format(len(pols)))
    #print("len(ans) = {}".format(len(ans)))
    #print("len(ALeigs) = {}".format(len(ALeigs)))

    GP_nfs = [
        { 'Nko': Nko,
          'SB': SturmBound,
          'chipoly': chipoly,
          'poly': pols[i],
          'ans': ans[i],
          'basis': bases[i],
          'ALeigs': ALeigs[i],
          'traces': traces[i],
        }   for i in range(nnf)]

    # We could return these as they are but the next processing step
    # will fail if the underlying gp process has quit, so we do the
    # processing here.

    # This processing returns full data but the polynomials have not
    # yet been polredbested and the an coefficients have not been
    # optimized (or even made integral):
    #return GP_nfs

    t1=time.time()
    if Detail:
        print("{}: finished constructing GP newforms (time {:0.3f})".format(Nko,t1-t0))
    nfs = [process_GP_nf(gp, nf, dmax, Detail) for nf in GP_nfs]
    if len(nfs)>1:
        nfs.sort(key=lambda f: f['traces'])
    t2=time.time()
    if Detail:
        print("{}: finished first processing of newforms (time {:0.3f})".format(Nko,t2-t1))
        if Detail>2:
            for nf in nfs:
                if 'eigdata' in nf:
                    print(nf['eigdata']['ancs'])
    nfs = [bestify_newform(nf,dmax,Detail) for nf in nfs]
    t3=time.time()
    if Detail:
        print("{}: finished bestifying newforms (time {:0.3f})".format(Nko,t3-t2))
        if Detail>2:
            for nf in nfs:
                if 'eigdata' in nf:
                    print(nf['eigdata']['ancs'])
    nfs = [integralify_newform(nf,dmax,Detail) for nf in nfs]
    t4=time.time()
    if Detail:
        print("{}: finished integralifying newforms (time {:0.3f})".format(Nko,t4-t3))
        if Detail>2:
            for nf in nfs:
                if 'eigdata' in nf:
                    print(nf['eigdata']['ancs'])
        print("Total time for space {}: {:0.3f})".format(Nko,t4-t0))
    gp.quit()
    return nfs

def process_GP_nf(gp, GP_nf, dmax=20, Detail=0):
    r"""
    Input is a dict with keys 'Nko' (N,k,chi_number), 'chipoly',  'SB' (Sturm bound), 'GP_newform',  'poly',  'ans',   'ALeigs', 'traces'

    Output adds 'traces' (unless already computed), and also 'eigdata' if 1<dimension<=dmax
    We do not yet use polredbest or optimize an coeffients

    NB This must be called on  each newform *before* the GP process associated with the data has been terminated.

    """
    Nko = GP_nf['Nko']
    chipoly = GP_nf['chipoly']
    poly = GP_nf['poly']
    SB = GP_nf['SB']
    ALeigs = GP_nf['ALeigs']
    traces = GP_nf['traces']
    assert traces # not None
    ans = GP_nf['ans']
    basis = GP_nf['basis']

    # initialize with data needing no more processing:

    newform = {'Nko': Nko, 'chipoly': chipoly, 'SB': SB, 'ALeigs':ALeigs, 'traces':traces}

    # Set the polynomial.  poly is the relative polynomial, in x (so
    # just x if the top degree is 1) with coefficients either integers
    # (if the bottom degree is 1) or polmods with modulus chipoly.
    #  rel_poly is in Qchi[x].

    Qx = PolynomialRing(QQ,'x')
    Qchi = NumberField(chipoly,'t')
    Qchi_x = PolynomialRing(Qchi,'x')
    chi_degree = chipoly.degree()

    rel_poly = gp2sage_ypoly(poly, Qchi_x)
    rel_degree = rel_poly.degree()

    newform['dim'] = dim = chi_degree*rel_degree
    small = (dmax==0) or (dim<=dmax)

    # for 'small' spaces we compute more data, where 'small' means
    # dimension<=dmax (unless dmax==0 in which case all spaces are
    # deemed small).  However spaces of dimension 1 never need the
    # additional data.

    if Detail:
        print("{}: degree = {} = {}*{}".format(Nko, dim, chi_degree, rel_degree))
        if Detail>1:
            print("rel_poly for {} is {}".format(Nko,rel_poly))

    # The newform has its 'traces' field set already. We will have set
    # its 'ans' field where relevant (1<dim<=dmax) to a list of lists
    # of coefficients in Qchi.  In the genuinely relative case we'll
    # need to absolutise these.

    if Detail>1: print("raw ans = {}".format(ans))

    # dimension 1 spaces: little to do

    if dim==1:  # e.g. (11,2,1)[0]
        newform['poly'] = Qx.gen()
        return newform

    # no more data required for non-small spaces:

    if not small:
        return newform

    if chi_degree==1: # e.g. (13,4,1)[1]; now rel_degree>1
        # field is not relative, ans are lists of integers, coeffs w.r.t. basis
        t0=time.time()
        ancs = ans.sage()
        t1 = time.time()
        if Detail:
            print("time for converting an coeffs to QQ = {}".format(t1-t0))
            if Detail>1:
                print("Coefficient vectors of ans: {}".format(ancs))
        newform['poly'] = poly = Qx(rel_poly)
        # basis is a gp matrix over Q
        basis = basis.sage()

        newform['eigdata'] = {
            'pol': poly.list(),
            'bas': basis,
            'n': 0, # temporary
            'm': 0, # temporary
            'ancs': ancs,
            }

        return newform

    if rel_degree==1: # e.g. (25,2,4)[0]; now chi_degree>1

        # the field is not relative; ans is a lists of 1-lists of
        # t_POLMOD modulo a GP poly in t, so we lift them and take
        # their coefficient vector to get the coordinates w.r.t. a
        # power basis for the field defined by chipoly.

        t0=time.time()
        ancs = [an[1].lift().Vecrev(dim).sage() for an in ans] # list of lists of integers/rationals
        t1 = time.time()
        if Detail:
            print("time for converting an coeffs to QQ = {}".format(t1-t0))
            if Detail>1:
                print("Coefficient vectors of ans: {}".format(ancs))
        newform['poly'] = poly = Qx(chipoly)
        # basis is a 1x1 gp matrix over Qchi, so we want the power basis for Qchi: trivial
        basis = [[int(i==j) for j in range(dim)] for i in range(dim)]

        newform['eigdata'] = {
            'pol': poly.list(),
            'bas': basis,
            'n': 0, # temporary
            'm': 0, # temporary
            'ancs': ancs,
            }

        return newform

    # Now we are in the genuinely relative case where chi_degree>1 and rel_degree>1
    # e.g. (25,2,5)

    # Now ans is a (python) list of nan (GP) lists of d_rel elements
    # of Qchi, and basis is a GP d_rel x d_rel matrix over Qchi

    #Setting the Hecke field as a relative extension of Qchi and as an absolute field:

    t0=time.time()
    Frel  = Qchi.extension(rel_poly,'b')
    abs_poly = Frel.absolute_polynomial()
    newform['poly'] = abs_poly(Qx.gen())
    t1 = time.time()
    if Detail:
        print("absolute poly = {}".format(abs_poly))
        if Detail>1:
            print("Time to construct Frel and find absolute poly = {}".format(t1-t0))
    Fabs = Frel.absolute_field('a')
    rel2abs = Fabs.structure()[1] # the isomorphism Frel --> Fabs
    z = rel2abs(Qchi.gen())
    zpow = [z**i for i in range(chi_degree)]
    # convert basis to a Sage list of lists of elements of Qchi:
    our_basis_coeffs = [[gp2sage_tpolmod(basis[i+1,j+1],Qchi) for j in range(rel_degree)] for i in range(rel_degree)]
    #print("our basis coeffs: {}".format(our_basis_coeffs))
    our_basis_rel = [Frel(b) for b in our_basis_coeffs]
    #print("our basis (Sage, relative): {}".format(our_basis_rel))
    our_basis_abs = [rel2abs(b) for b in our_basis_rel]
    #print("our basis (Sage, absolute): {}".format(our_basis_abs))
    basis = sum([[(zpowi*yj).list() for zpowi in zpow] for yj in our_basis_abs],[])
    #print("basis (Sage, matrix/Q): {}".format(basis))
    t2 = time.time()
    if Detail>1:
        print("Time to construct Fabs and y,z in Fabs and basis matrix = {}".format(t2-t1))

    #  Convert coordinates of the an.  After lifting these are lists
    #  of lists of polynomials in Q[t] so simply extracting
    #  coefficient vectors gives their coordinates in terms of the
    #  basis z^i*y_j where Qchi=Q(z) and [y_1,...,y_d_rel] is the
    #  Qchi-basis of Frel.  To relate these to the power basis of Fabs
    #  we only need the change of basis matrix whose rows give the
    #  power basis coefficients of each z^i*y_j (in the right order).

    ancs = [[c.lift().Vecrev(chi_degree).sage() for c in an] for an in ans]
    t4 = time.time()
    if Detail>1:
        print("Time to construct ancs) = {}".format(t4-t2))
    ancs = [sum([anci for anci in anc],[]) for anc in ancs]
    if Detail>1:
        print("Coefficient vectors of ans: {}".format(ancs))

    newform['eigdata'] = {
        'pol': abs_poly.list(),
        'bas': basis,
        'n': 0, # temporary
        'm': 0, # temporary
        'ancs': ancs,
    }

    return newform

def bestify_newform(nf, dmax=20, Detail=0):
    r"""
    Input is a dict with keys
     {
    'Nko',  'chipoly', 'SB', 'ALeigs', 'dim', 'traces', 'poly', 'eigdata'
    }
    (with ALeigs only when o=1 and eigdata only when 1<dim<=dmax)

    Here eigdata is a dict of the form

    'pol': list of d+1 coefficients of polynomial defining Hecke field F
    'bas': list of lists of rationals holding dxd matrix whose rows define a Q-basis for F in terms of the power basis
    'ancs': list of lists of d rationals giving coefficients of each a_n w.r.t. that basis
    'n': 0 (not yet set)
    'm': 0 (not yet set)

    Output adds 'best_poly' and applies a change of basis to eigdata
    changing 'pol' and 'bas' so the basis coefficients are w.r.t. the
    best_poly power basis and not the poly power basis.
    """
    Nko = nf['Nko']
    dim = nf['dim']
    if dim==1:
        nf['best_poly'] = nf['poly']
        return nf
    if dim>dmax:
        nf['best_poly'] = None
        return nf
    poly = nf['poly']
    if Detail:
        print("non-best poly for {} is {}".format(Nko,poly))
    nf['best_poly'] = best_poly = polredbest_stable(poly)
    if Detail:
        print("best_poly for {} is {}".format(Nko,best_poly))
    if dim>dmax:
        return nf

    # Now the real work starts
    Fold = NumberField(poly,'a')
    Fnew = NumberField(best_poly,'b')
    #iso = Fold.embeddings(Fnew)[0] # we do not care which isomorphism
    iso = Fold.is_isomorphic(Fnew,isomorphism_maps=True)[1][0] # we do not care which isomorphism
    Qx = PolynomialRing(QQ,'x')
    #x = Qx.gen()
    iso = Fold.hom([Qx(iso)(Fnew.gen())])
    new_basis_matrix = [a.list() for a in [iso(b) for b in [Fold(co) for co in nf['eigdata']['bas']]]]
    nf['eigdata']['bas'] = new_basis_matrix
    nf['eigdata']['pol'] = best_poly.list()
    return nf

def integralify_newform(nf, dmax=20, Detail=0):
    r"""
    Input is a dict with keys
     {
    'Nko',  'chipoly', 'SB', 'ALeigs', 'dim', 'traces', 'poly', 'best_poly', 'eigdata'
    }
    (with ALeigs only when o=1 and eigdata only when 1<dim<=dmax)

    Output changes eigdata['bas'] and eigdata['ancs'] so the latter are all integral and small, when 1<dim<=dmax.
    """
    dim = nf['dim']
    if 1<dim and  dim<=dmax:
        nf['eigdata'] = eigdata_reduce(nf['eigdata'], nf['SB'], Detail)
    return nf

def eigdata_reduce(eigdata, SB, Detail=0):
    newcoeffs, newbasis = coeff_reduce(eigdata['ancs'], eigdata['bas'], SB, Detail)
    eigdata['bas'] = newbasis
    eigdata['ancs'] = newcoeffs
    return eigdata

def coeff_reduce(C, B, SB, Detail=0, debug=False):
    """B is a list of lists of rationals holding an invertible dxd matrix
    C is a list of lists of rationals holding an nxd matrix
    C*B remains invariant
    SB = Sturm bound: the first SB rows of C should span the whole row space over Z

    Computes invertible U and returns (C', B') = (C*U, U^(-1)*B), so
    that the entries of C' are integers and 'small'
    """
    if Detail>1:
        print("Before LLL, coefficients:\n{}".format(C))
    # convert to actual matrices:
    d = len(B)
    B=Matrix(B)
    C=Matrix(C)
    if debug:
        CB=C*B
    # Make integral:
    C1, den = C._clear_denom()
    B1 = B/den
    if Detail and den>1:
        print("denominator = {}".format(den))
    # Make primitive:
    S, V1, V2 = C1.smith_form(transformation=True)
    S = S.submatrix(nrows=d)
    #print("About to invert matrices of size {}, {}".format(S.dimensions(),V2.dimensions()))
    C2 = C1*V2*S**(-1)
    B2 = S*V2**(-1)*B1
    if debug:
        assert CB==C2*B2
    if Detail:
        scales = [S[i,i] for i in range(d)]
        if not all(s==1 for s in scales):
            print("scale factors {}".format(scales))
    # LLL-reduce (using only the first max(SB,d) rows of C):
    # d2=SB
    # C2chop = C2.submatrix(nrows=d2)
    # while C2chop.rank()<d:
    #     d2+=5
    #     C2chop = C2.submatrix(nrows=d2)
    C2chop = C2

    Cred = C2chop.transpose().LLL().transpose()
    # the unimodular transform is not returned, so we must compute it:
    U = C2chop * BackslashOperator() * Cred
    if debug:
        assert all(c in ZZ for c in U.list())
        print("U = {}\ndet(U)={}".format(U,U.det()))
        assert U.det() in [1,-1]
    Cred = C2*U
    #print("About to invert matrix of size {}".format(U.dimensions()))
    Bred = U**(-1)*B2
    # Check output is consistent with input:
    if debug:
        assert CB==Cred*Bred
    # Convert back to lists of lists
    Cred = [ci.list() for ci in Cred]
    Bred = [bi.list() for bi in Bred]
    if Detail>1:
        print("After LLL, coefficients:\n{}".format(Cred))
    return Cred, Bred

def str_nosp(x):
    return str(x).replace(" ","").replace("'","")

def data_to_string(N,k,o,t,newforms):
    r""" Given the newforms data for space (N,k,o) as produced by
    Newforms() in time t, creates an output string in the correct format
    """
    dims = str_nosp([f['dim'] for f in newforms])
    traces = [f['traces'] for f in newforms]
    traces = str_nosp(traces)
    ALeigs = [f['ALeigs'] for f in newforms]
    if o>1:
        ALeigs = '[]'
    else:
        ALeigs = [["<{},{}>".format(b[0],b[1]) for b in a] for a in ALeigs]
        ALeigs = str_nosp(ALeigs)
    polys = [f['best_poly'] for f in newforms]
    polys = [f.list() for f in polys if f] # excluded the "None"s
    polys = str_nosp(polys)
    cutters = cm = it = pra = "[]"

    def eig_data(f):
        edata = f['eigdata']
        pol = str(edata['pol'])
        bas = str(edata['bas'])
        n ='0' # temporary
        m ='0'
        e = str(edata['ancs'])
        return "<" + ",".join([pol, bas, n, m, e]) + ">"

    eigs = str_nosp([eig_data(f) for f in newforms if f['best_poly'] and f['dim']>1])

    return ":".join([str(N), str(k), str(o), "{:0.3f}".format(t), dims, traces, ALeigs, polys, cutters, eigs, cm, it, pra])

def DecomposeSpaces(filename, Nk2min, Nk2max, dmax=20, nan=100, njobs=1, jobno=0, Detail=0):
    out = open(filename, 'w') if filename else None
    screen = sys.stdout
    Nmax = int(Nk2max/4.0)
    nspaces=0
    n = 0 # will increment for each (N,k,chi) in range, so we skip unless n%njobs==jobno
    for N in range(1,Nmax+1):
        kmin = max(2,(RR(Nk2min)/N).sqrt().ceil())
        kmax = (RR(Nk2max)/N).sqrt().floor()
        if kmin>kmax:
            continue
        level_info = "N = {}: ".format(N)
        level_info += "{} <=k<= {} ".format(kmin,kmax)
        #level_info += "({} <=Nk^2<= {})".format(N*kmin**2,N*kmax**2)
        #screen.write(level_info)
        info_written=False
        Chars = DirichletCharacterGaloisReps(N)
        for k in range(kmin, kmax+1):
            if not info_written:
                screen.write(level_info)
                info_written=True
            screen.write(" [k={}] ".format(k))
            nspaces+=1

            for i in range(len(Chars)):
                n += 1
                if n%njobs!=jobno:
                    continue

                screen.write(" (o={}) ".format(i+1))
                t0=time.time()
                newforms = NewformTraces(N,k,i+1,dmax,nan, Detail)
                t0=time.time()-t0
                line = data_to_string(N,k,i+1,t0,newforms) + "\n"
                if out:
                    out.write(line)
                else:
                    screen.write('\n')
                    screen.write(line)
        if info_written:
            screen.write('\n')
    if out:
        out.close()
    #return nspaces


def Nspaces(Nk2min,Nk2max):
    Nmax = int(Nk2max/4.0)
    nspaces=0
    for N in range(1,Nmax+1):
        kmin = max(2,(RR(Nk2min)/N).sqrt().ceil())
        kmax = (RR(Nk2max)/N).sqrt().floor()
        if kmin>kmax:
            continue
        nspaces += NChars(N)*(1+kmax-kmin)
    return nspaces

def WeightOne(filename, Nmin, Nmax, dmax, nan=100, njobs=1, jobno=0, Detail=0):
# Outputs N:k:i:time:dims:traces:polys with polys only for dims<=dmax
    out = open(filename, 'w') if filename else None
    screen = sys.stdout
    for N in range(Nmin,Nmax+1):
        if N%njobs!=jobno:
            continue
        screen.write("N = {}: ".format(N))
        Chars = DirichletCharacterGaloisReps(N)
        for i in range(len(Chars)):
            screen.write(" (o={}) ".format(i+1))
            t0=time.time()
            newforms = NewformTraces(N,1,i+1,dmax,nan, Detail)
            t0=time.time()-t0
            line = data_to_string(N,1,i+1,t0,newforms) + "\n"
            if out:
                out.write(line)
            else:
                screen.write('\n')
                screen.write(line)
        screen.write('\n')
    if out:
        out.close()

from char import DirichletCharacterGaloisReps
from mf_compare import polredbest_stable#, polredbest, polredabs

from dirichlet_conrey import DirichletCharacter_conrey as DC
from sage.interfaces.gp import Gp
from sage.all import ZZ,QQ, RR, PolynomialRing, cyclotomic_polynomial, euler_phi, NumberField, primes, LCM
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
        return deg*QQ(x)
    try:
        #print("---returns(3) {}".format(x.trace().sage()))
        return x.trace().sage()
    except NameError:
        return x.trace().trace().sage()

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
    pols = gp.mfsplit(Snew)
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

    # Get the character polynomial

    # Note that if the character order is 2*m with m odd then Pari uses the
    # m'th cyclotomic polynomial and not the 2m'th (e.g. for a
    # character of order 6 it uses t^2+t+1 and not t^2-t+1).

    chi_order_2 = chi_order//2 if chi_order%4==2 else chi_order
    chipoly = cyclotomic_polynomial(chi_order_2,'t')
    chi_degree = chipoly.degree()
    assert chi_degree==euler_phi(chi_order)==euler_phi(chi_order_2)
    if Detail>1:
        print("chipoly = {}".format(chipoly))

    # Get the polynomials:  these are polynomials in y with coefficients either integers or polmods with modulus chipoly

    pols = gp.mfsplit(Snew)[2]
    if Detail>2: print("pols[GP] = {}".format(pols))

    # Get the coefficients an:

    coeffs = gp.mfcoefs(Snew,nan)
    ans = [coeffs*gp.mftobasis(Snew,nf) for nf in newforms]
    if Detail>2: print("ans[GP] = {}".format(ans))

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

    Nko = (N,k,chi_number),
    GP_nfs = [
        { 'Nko': Nko,
          'chipoly': chipoly,
          'GP_newform': newforms[i+1],
          'poly': pols[i+1],
          'ans': ans[i],
          'ALeigs': ALeigs[i],
        }   for i in range(nnf)]

    # We could return these as they are but the next processing step
    # will fail if the underlying gp process has quite, so we do the
    # processing here.

    # This processing returns full data but the polynomials have not
    # yet been polredbested and the an coefficients have not been
    # optimized (or even made integral):
    #return GP_nfs

    t1=time.time()
    if Detail:
        print("{}: finished constructing GP newforms (time {:0.3f})".format(Nko,t1-t0))
    nfs = [process_GP_nf(nf, dmax, Detail) for nf in GP_nfs]
    if len(nfs)>1:
        nfs.sort(key=lambda f: f['traces'])
    t2=time.time()
    if Detail:
        print("{}: finished processing newforms (time {:0.3f})".format(Nko,t2-t1))
    nfs = [bestify_newform(nf,dmax,Detail) for nf in nfs]
    t3=time.time()
    if Detail:
        print("{}: finished bestifying newforms (time {:0.3f})".format(Nko,t3-t2))
        print("Total time for space {}: {:0.3f})".format(Nko,t3-t0))
    gp.quit()
    return nfs

def process_GP_nf(GP_nf, dmax=20, Detail=0):
    r"""
    Input is a dict of the form
    {'Nko': (N,k,chi_number),
    'chipoly': chipoly,
    'GP_newform': newforms[i+1],
    'poly': pols[i+1],
    'ans': ans[i+1],
    'ALeigs': ALeigs[i]}

    Output adds 'traces', and also 'eigdata' if 1<dimension<=dmax
    We do not yet use polredbest or optimize an coeffients

    NB This must be called on  each newform *before* the GP process associated with the data has been terminated.

    """
    Nko = GP_nf['Nko']
    chipoly = GP_nf['chipoly']
    ALeigs = GP_nf['ALeigs']

    # initialize with data needing no more processing:

    newform = {'Nko': Nko, 'chipoly': chipoly, 'ALeigs':ALeigs}

    # Set the polynomial.  This is a polynomial in y, (just y if the
    # top degree is 1) with coefficients either integers (if the
    # bottom degree is 1) or polmods with modulus chipoly.  In all
    # cases rel_poly will be in Qchi[y].

    Qchi = NumberField(chipoly,'z')
    Qchi_y = PolynomialRing(Qchi,'y')
    chi_degree = chipoly.degree()

    rel_poly = gp2sage_ypoly(GP_nf['poly'], Qchi_y)
    rel_degree = rel_poly.degree()

    newform['dim'] = dim = chi_degree*rel_degree
    small = (dmax==0) or (dim<=dmax)

    # for 'small' spaces we compute more data, where 'small' means
    # dimension<=dmax (unless dmax==0 in which case all spaces are
    # deemed small).  However spaces of dimension 1 never need the
    # additional data.

    if Detail:
        print("{}: degree = {} = {}*{}".format(Nko, dim, chi_degree, rel_degree))
        print("rel_poly for {} is {}".format(Nko,rel_poly))

    # In all cases we extract traces from the GP ans:
    ans = GP_nf['ans']
    if Detail>1: print("raw ans = {}".format(ans))

    # dimension 1 spaces: special case simpler traces, and no more to do:

    Qx = PolynomialRing(QQ,'x')
    x = Qx.gen()
    if dim==1:  # e.g. (11,2,1)[0]
        newform['traces'] = [ZZ(a) for a in ans][1:]
        newform['poly'] = x
        if Detail>1: print("traces = {}".format(newform['traces']))
        return newform

    # All dimensions >1: traces

    traces = [abstrace(an,dim) for an in ans][1:]
    # fix up trace(a_1)
    traces[0]=dim
    if Detail>1: print("traces = {}".format(traces))
    newform['traces'] = traces

    # no more data required for non-small spaces:

    if not small:
        return newform

    if chi_degree==1 or rel_degree==1: # e.g. (13,4,1)[1] or (25,2,4)[0] respectively

        # field is not relative, ans are t_POLMOD modulo GP_pol in y
        # or t, so if we lift them and take their coefficient vector
        # we'll get the coordinates w.r.t. a power basis for the field
        # defined by either rel_poly or chipoly.
        ancs = [an.lift().Vecrev(dim) for an in ans][1:]
        ancs = [[QQ(c) for c in an] for an in ancs]
        basis = [[int(i==j) for j in range(dim)] for i in range(dim)]
        newform['poly'] = poly = Qx(rel_poly) if chi_degree==1 else Qx(chipoly)
        # change variable (otherwise polredbest may complain of variable order)
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

    #Setting the Hecke field as a relative extension of Qchi and as an absolute field:

    t0=time.time()
    Frel  = Qchi.extension(rel_poly,'b')
    abs_poly = Frel.absolute_polynomial()
    newform['poly'] = abs_poly(x)
    t1 = time.time()
    if Detail:
        print("absolute poly = {}".format(abs_poly))
        print("Time to construct Frel and find absolute poly = {}".format(t1-t0))
    Fabs = Frel.absolute_field('a')
    rel2abs = Fabs.structure()[1] # the isomorphism Frel --> Fabs
    z = rel2abs(Qchi.gen())
    y = rel2abs(Frel.gen())
    t2 = time.time()
    if Detail:
        print("Time to construct Fabs and y,z in Fabs = {}".format(t2-t1))

    #  Get coordinates of the an.  After lifting twice these are
    #  polynomials in Q[t][y] so simply extracting coefficient vectors
    #  gives their coordinates in terms of the basis z^i*y^j where
    #  Qchi=Q(z) and F=Qchi(y).  To relate these to the power basis of
    #  Fabs we only need the change of basis matrix whose rows give
    #  the power basis coefficients of each z^i*y^j (in the right
    #  order).

    ancs = [[c.lift().Vecrev(chi_degree) for c in a.lift().Vecrev(rel_degree)] for a in ans][1:]
    t4 = time.time()
    if Detail:
        print("Time to construct ancs (part 1) = {}".format(t4-t2))
    ancs = [[[QQ(ci) for ci in c] for c in an] for an in ancs]
    t5 = time.time()
    if Detail:
        print("Time to construct ancs (part 2) = {}".format(t5-t4))
    ancs = [sum([anci for anci in anc],[]) for anc in ancs]
    t6 = time.time()
    if Detail:
        print("Time to construct ancs (part 3) = {}".format(t6-t5))
    if Detail>1:
        print("Coefficient vectors (before scaling) of ans: {}".format(ancs))
    # find a common denominator for the i'th coefficients, for each i
    scales = [LCM([anc[i].denominator() for anc in ancs]) for i in range(dim)]
    integral = all(c==1 for c in scales)
    if not integral:
        if Detail:
            print("*******Not all coefficients are integral, rescaling by {}".format(scales))
        ancs = [[s*anc for s,anc in zip(scales,an)] for an in ancs]
    zpow = [z**i for i in range(chi_degree)]
    ypow = [y**j for j in range(rel_degree)]
    basis = sum([[(zpowi*ypowj).list() for zpowi in zpow] for ypowj in ypow],[])
    if not integral:
        basis = [[bi/s for s,bi in zip(scales,b)] for b in basis]
    assert all(all(anc in ZZ for anc in an) for an in ancs)
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
    'Nko',  'chipoly', 'ALeigs', 'dim', 'traces', 'poly', 'eigdata'
    }
    (withe ALeigs only when o=1 and eigdata only when 1<dim<=dmax)

    Output adds 'best_poly' and applies a change of basis to eigdata
    so the basis coefficients are w.r.t. the best_poly power basis and
    not the poly power basis.
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
        print("non-best poly for {} is {} (parent {})".format(Nko,poly,poly.parent()))
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
    x = Qx.gen()
    iso = Fold.hom([Qx(iso)(Fnew.gen())])
    new_basis_matrix = [a.list() for a in [iso(b) for b in [Fold(co) for co in nf['eigdata']['bas']]]]
    nf['eigdata']['bas'] = new_basis_matrix
    nf['eigdata']['pol'] = best_poly.list()
    return nf

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

def DecomposeSpaces(filename, Nk2bound, dmax, nan=100, njobs=1, jobno=0, Detail=0):
# Outputs N:k:i:time:dims:traces:polys with polys only for dims<=dmax
    out = open(filename, 'w') if filename else None
    screen = sys.stdout
    Nmax = int(Nk2bound/4.0)
    for N in range(1,Nmax+1):
        screen.write("N = {}: ".format(N))
        Chars = DirichletCharacterGaloisReps(N)
        kmax = int((RR(Nk2bound)/N).sqrt())
        for k in range(2, kmax+1):
            if (N+k)%njobs!=jobno:
                #screen.write("Skipping (N,k)=({},{}) since (N+k)%{}={}, not {}".format(N,k,njobs,(N+k)%njobs,jobno))
                continue
            screen.write(" [k={}] ".format(k))
            for i in range(len(Chars)):
                screen.write(" (o={}) ".format(i+1))
                t0=time.time()
                newforms = Newforms(N,k,i+1,dmax,nan, Detail)
                t0=time.time()-t0
                line = data_to_string(N,k,i+1,t0,newforms) + "\n"
                if out:
                    out.write(line)
                else:
                    screen.write('\n')
                    screen.write(line)
        screen.write('\n')
    if out:
        out.close()

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
            newforms = Newforms(N,1,i+1,dmax,nan, Detail)
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

from char import DirichletCharacterGaloisReps

from dirichlet_conrey import DirichletCharacter_conrey as DC
from sage.interfaces.gp import Gp
from sage.all import ZZ,QQ, RR, PolynomialRing, cyclotomic_polynomial, euler_phi, NumberField
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
    if deg==1:
        return x.sage()
    if x in QQ: # miraculously this works for a GpElement
        return deg*QQ(x)
    try:
        return x.trace().sage()
    except NameError:
        return x.trace().trace().sage()


def Newforms(N, k, chi_number, dmax=20, nan=100, verbose=False):
    # N and k are Sage ints but chi is a gp vector
    Chars = DirichletCharacterGaloisReps(N)
    if chi_number<1 or chi_number>len(Chars):
        print("Character number {} out of range for N={} (should be between 1 and {})".format(chi_number,N,len(Chars)))
        return []
    gp = Gp(logfile="gp.log") # A new gp interface for each space
    gp.default('parisizemax',64000000000)
    G = gp.znstar(N,1)
    chi_sage = Chars[chi_number-1]
    chi_gp = gp.znconreylog(G,DC.number(chi_sage))
    Snew = gp.mfinit([N,k,[G,chi_gp]],0)
    chi_order = DC.multiplicative_order(chi_sage)
    if verbose: print("(N,k,c) = ({},{},{}), character order {}: gp char code = {}".format(N,k,chi_number,chi_order,chi_gp))
    newforms = gp.mfeigenbasis(Snew)
    nnf = len(newforms)
    if nnf==0:
        return []
    if verbose: print("Number of newforms = {}".format(nnf))

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
    if verbose: print("chipoly = {}".format(chipoly))

    Qchi = NumberField(chipoly,'z')
    if verbose: print("Q(chi) = {}".format(Qchi))

    # Setting the polynomials.  These are polynomials in y with coefficients either integers or polmods with modulus chipoly

    Qchi_y = PolynomialRing(Qchi,'y')
    if verbose: print("Q(chi)[y] = {}".format(Qchi_y))
    pols = gp.mfsplit(Snew) # ,flag=1)
    #if verbose: print("Before conversion, pols = {}".format(pols[2]))
    pols = [gp2sage_ypoly(f, Qchi_y) for f in pols[2]]
    if verbose: print("pols = {}".format(pols))

    # Setting the dimensions list (absolute degrees)

    dims = [chi_degree*f.degree() for f in pols]
    nnf0 = len([d for d in dims if d<=dmax])
    if verbose:
        print("dims = {}, so {} newforms have dimensions <={}".format(dims,nnf0,dmax))

    #Setting the Hecke fields as relative extensions of Qchi and as absolute fields:

    Hecke_fields_relative  = [Qchi.extension(f,'b') for f in pols[:nnf0]]
    abs_polys = [F.absolute_polynomial() for F in Hecke_fields_relative]
    if verbose: print("absolute pols = {}".format(abs_polys))
    Hecke_fields_absolute = [F.absolute_field('a') for F in Hecke_fields_relative]
    isoms = [F.structure()[1] for F in Hecke_fields_absolute]

    # if verbose:
    #     print("Relative  Hecke fields: {}".format(Hecke_fields_relative))
    #     print("Absolute Hecke fields: {}".format(Hecke_fields_absolute))

    # Compute an's and convert to elements of the (relative) Hecke field:

    coeffs = gp.mfcoefs(Snew,nan)
    ans = [coeffs*gp.mftobasis(Snew,nf) for nf in newforms]
    # Alternative method for traces:
    traces = [[abstrace(a,d) for a in ansi] for ansi,d in zip(ans,dims)]
    if verbose: print("traces = {}".format(traces))

    if verbose: print("about to convert ans...")
    ans = [gp2sage_anfelt_list(ansi, iso) for ansi, iso in zip(ans[:nnf0], isoms)]
    if verbose: print("finished")

    # do not omit a_0 so indexing is natural

    #if verbose: print("ans2 = {}".format(ans2))

    # Compute AL-eigenvalues if character is trivial:
    if chi_order==1:
        Qlist = [p**e for p,e in ZZ(N).factor()]
        ALs = [gp.mfatkineigenvalues(Snew,Q).sage() for Q in Qlist]
        if verbose: print("ALs: {}".format(ALs))
        # "transpose" this list of lists:
        ALeigs = [[[Q,ALs[i][j][0]] for i,Q in enumerate(Qlist)] for j in range(nnf)]
        if verbose: print("ALeigs: {}".format(ALeigs))
    else:
        ALeigs = [[] for _ in range(nnf)]

    all_nf = [
        {'dim': dims[i],
         'chipoly': chipoly,
         'poly': pols[i] if i<nnf0 else None,
         'abs_poly': abs_polys[i] if i<nnf0 else None,
         'traces': traces[i],
         'ans': ans[i] if i<nnf0 else None,
         'ALeigs': ALeigs[i]}   for i in range(nnf)]
    if nnf>1:
        all_nf.sort(key=lambda f: f['traces'])
    return all_nf

def DecomposeSpaces(filename, Nk2bound, dmax, nan=100, njobs=1, jobno=0):
# Outputs N:k:i:time:dims:traces:polys with polys only for dims<=dmax
    out = open(filename, 'w') if filename else None
    screen = sys.stdout
    Nmax = int(Nk2bound/4.0)
    for N in range(1,Nmax+1):
        screen.write("N = {}: ".format(N))
        Chars = DirichletCharacterGaloisReps(N)
        kmax = int((RR(Nk2bound)/N).sqrt())
        for k in range(2, kmax+1):
            if(N+k)%njobs!=jobno:
                break
            screen.write(" [k={}] ".format(k))
            for i in range(len(Chars)):
                t0=time.time()
                data = Newforms(N,k,i+1,dmax,nan)
                dims = [dat['dim'] for dat in data]
                traces = [dat['traces'][1:] for dat in data]
                traces = str(traces).replace(" ","")
                ALeigs = [dat['ALeigs'] for dat in data]
                ALeigs = [["<{},{}>".format(b[0],b[1]) for b in a] for a in ALeigs]
                ALeigs = str(ALeigs).replace(" ","").replace("'","")
                polys = [dat['abs_poly'] for dat in data]
                polys = [f.list() for f in polys if f] # excluded the "None"s
                polys = str(polys).replace(" ","")
                ans = [dat['ans'] for dat in data]
                ans = [[an.list() if dimi>1 else [an] for an in ansi[1:]] for ansi,dimi in zip(ans,dims) if ansi] # excluded the "None"s
                ans = str(ans).replace(" ","")
                t0=time.time()-t0
                if out:
                    out.write("{N}:{k}:{i}:{t:0.3f}:{D}:{T}:{A}:{F}::{E}:::\n".format(
                        N=N,k=k,i=i+1,t=t0,D=dims,T=traces,A=ALeigs,F=polys,E=ans))
        screen.write('\n')


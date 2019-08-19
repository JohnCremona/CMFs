from char import NChars, char_orbit_index_to_DC_number
from mf_compare import polredbest_stable#, polredbest, polredabs

from sage.all import pari,ZZ,QQ, Rational,RR, GF, PolynomialRing, cyclotomic_polynomial, euler_phi, NumberField, Matrix, prime_range
from sage.rings.finite_rings.integer_mod import mod
from sage.libs.pari.convert_sage import gen_to_sage
from sage.libs.pari.all import PariError
import sys
import time

Qt = PolynomialRing(QQ,'t')

# some pari utilities

pari_x = pari("x")
pari_col1 = pari("M -> M[,1]")
pari_trace_product = pari("(M1,M2) -> [m,n]=matsize(M1); sum(i=1,m,sum(j=1,n,M1[i,j]*M2[j,i]))")
def pari_row_slice(r1,r2):
    return pari("M -> M[{}..{},]".format(r1,r2))
def pari_trace(d):
    return pari('c->if(type(c)=="t_POLMOD",trace(c),c*{})'.format(d))
def pari_e1(d):
    return pari("{}~".format([int(j==0) for j in range(d)]))


def abstrace(x,deg):
    # absolute trace of a gp int / polmod / polmod pver polmod
    # trace of a t_POLMOD does what is expected but trace of an int
    # doubles it.  Also we might see an int as one coefficient of a newform
    # most of whose coefficients are t_POLMODs.  In this case we need to
    # multiply by the appropriate degree, so have to pass the degree as a
    # parameter.
    #print("abstrace({}) in degree {}".format(x,deg))
    if deg==1:
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
    G = pari(N).znstar(1)
    chi_dc = char_orbit_index_to_DC_number(N,chi_number)
    chi_gp = G.znconreylog(chi_dc)
    chi_order = ZZ(G.charorder(chi_gp))
    chi_degree = euler_phi(chi_order)
    if Detail:
        print("order(chi) = {}, [Q(chi):Q] = {}".format(chi_order, chi_degree))
        print("pari character = {}".format(chi_gp))
    NK = [N,k,[G,chi_gp]]
    Snew = pari(NK).mfinit(0)
    rel_degree = Snew.mfdim()
    dim = chi_degree*rel_degree
    if Detail:
        print("Relative dimension = {}".format(rel_degree))
        print("dim({}:{}:{}) = {}*{} = {}".format(N,k,chi_number,chi_degree,rel_degree,dim))
    return NK, Snew

def is_semisimple_modular(M, m,  nprimes=5):
    """M is a pari matrix over Q(zeta_m).  Check if M mod p has squarefree
    char poly for nprimes primes p=1 (mod m).  If True for any p,
    return True since then the char poly of M itself must be
    square-free.  If False for all p, return False since the M
    probably has non-squarefree char poly.  There may therefore be
    false negatives.
    """
    pol = cyclotomic_polynomial(m)
    pt = pari("t")
    np=0
    for p in prime_range(1000000):
        if m>1 and not p%m==1:
            continue
        np+=1
        #print("testing modulo p={}".format(p))
        if np>nprimes:
            #print("op not semisimple modulo {} primes, so returning False".format(nprimes))
            return False
        zmodp = pari(pol.roots(GF(p))[0][0])
        #print("zmodp = {}".format(zmodp))
        try:
            Mmodp = M.lift()*pari(mod(1,p))
            #print("Lifted matrix = {}".format(Mmodp))
            Mmodp = Mmodp.subst(pt,zmodp)
            #print("matrix (mod {}) = {}".format(p,Mmodp))
            modpcharpoly = Mmodp.charpoly()
            #print("char poly (mod {}) = {}".format(p,modpcharpoly))
            if modpcharpoly.issquarefree():
                #print("op is semisimple mod {}".format(p))
                return True
            else:
                #print("op is not semisimple mod {}".format(p))
                pass
        except PariError: ## happens if M not integral mod p
            np-=1


def Newforms_v1(N, k, chi_number, dmax=20, nan=100, Detail=0):
    t0=time.time()
    G = pari(N).znstar(1)
    chi_dc = char_orbit_index_to_DC_number(N,chi_number)
    chi_gp = G.znconreylog(chi_dc)
    chi_order = ZZ(G.charorder(chi_gp))
    if Detail:
        print("Decomposing space {}:{}:{}".format(N,k,chi_number))
    NK = [N,k,[G,chi_gp]]
    pNK = pari(NK)
    if Detail>1:
        print("NK = {} (gp character = {})".format(NK,chi_gp))
    SturmBound = pNK.mfsturm()
    Snew = pNK.mfinit(0)
    reldim = Snew.mfdim()
    if reldim==0:
        if Detail:
            print("The space {}:{}:{} is empty".format(N,k,chi_number))
        return []

    # Get the character polynomial
    # Note that if the character order is 2*m with m odd then Pari uses the
    # m'th cyclotomic polynomial and not the 2m'th (e.g. for a
    # character of order 6 it uses t^2+t+1 and not t^2-t+1).

    chi_order_2 = chi_order//2 if chi_order%4==2 else chi_order
    chipoly = cyclotomic_polynomial(chi_order_2,'t')
    chi_degree = chipoly.degree()
    totdim = reldim * chi_degree
    assert chi_degree==euler_phi(chi_order)==euler_phi(chi_order_2)
    if Detail:
        print("Computed newspace {}:{}:{}, dimension={}*{}={}, now splitting into irreducible subspaces".format(N,k,chi_number, chi_degree, reldim, totdim))
        if Detail>1:
            print("Sturm bound = {}".format(SturmBound))
            print("character order = {}".format(chi_order))

    # Get the relative polynomials:  these are polynomials in y with coefficients either integers or polmods with modulus chipoly
    # But we only need the poly for the largest space if its absolute dimension is less than 20
    d = max(reldim // 2, dmax // chi_degree) if dmax else 0
    if Detail: t1=time.time(); print("...calling mfsplit({},{})...".format(d,d))
    forms, pols = Snew.mfsplit(d,d)
    if Detail: print("Call to mfsplit took {:.3f} secs".format(time.time()-t1))
    if Detail>2: print("mfsplit({},1) returned pols[GP] = {}".format(d,pols))
    dims = [chi_degree*f.poldegree() for f in pols]
    # We may be missing the largest newform, add its dimension in if needed
    d = totdim - sum(dims+[0])
    if d:
        dims += [d]
    nnf = len(dims)
    if Detail:
        print("The space {}:{}:{} has {} newforms, dimensions {}".format(N,k,chi_number,nnf,dims))

    # Compute trace forms using a combination of mftraceform and mfsplit (this avoids the need to compute a complete eigenbasis)
    # When the newspace contains a large irreducible subspace (and zero or more small ones) this saves a huge amount of time (e.g. 1000x faster)
    traces = [None for _ in range(nnf)]
    if Detail: t1=time.time(); print("...calling mftraceform...")
    straces = pNK.mftraceform().mfcoefs(nan)
    if Detail: print("Call to mftraceform took {:.3f} secs".format(time.time()-t1))
    straces = gen_to_sage(pari.apply(pari_trace(chi_degree),straces))
    if Detail>1: print("Newspace traceform: {}".format(straces))

    # Compute coefficients here (but note that we don't need them if there is only one newform and its dimension is > dmax)
    if nnf>1 or dmax==0 or dims[0] <= dmax:
        if Detail: t1=time.time(); print("...computing {} mfcoefs...".format(nan))
        coeffs = Snew.mfcoefs(nan)
        if Detail: print("Call to mfcoefs took {:.3f} secs".format(time.time()-t1))

    if nnf==1:
        traces[0] = straces[1:]
    else:
        if Detail: s0=time.time()
        tforms = [pari.apply("trace",forms[i]) if pols[i].poldegree() > 1 else forms[i] for i in range(nnf-1)]
        ttraces = [pari.apply(pari_trace(chi_degree),coeffs*nf) for nf in tforms]
        ltraces = [straces[i] - sum([ttraces[j][i] for j in range(len(ttraces))]) for i in range(nan+1)]
        traces = [list(t)[1:] for t in ttraces] + [ltraces[1:]]
        if Detail>1: print("Traceforms: {}".format(traces))
        if Detail: print("Spent {:.3f} secs computing traceforms".format(time.time()-s0))

    # Get coefficients an for all newforms f of dim <= dmax (if dmax is set)
    # Note that even if there are only dimension 1 forms we want to compute an so that pari puts the AL-eigenvalues in the right order
    # m = max([d for d in dims if (dmax==0 or d<=dmax)] + [0])
    d1 = len([d for d in dims if d == 1])
    dm = len([i for i in range(nnf) if dmax==0 or dims[i] <= dmax])
    ans = [traces[i] for i in range(d1)] + [coeffs*forms[i] for i in range(d1,dm)] + [None for i in range(dm,nnf)]
    if Detail>2: print("ans[GP] = {}".format(ans))
    newforms = [None for i in range(d1)] + [forms[i] for i in range(d1,dm)] + [None for i in range(dm,nnf)]

    # Compute AL-eigenvalues if character is trivial:
    if chi_order==1:
        Qlist = [(p,p**e) for p,e in ZZ(N).factor()]
        ALs = [gen_to_sage(Snew.mfatkineigenvalues(Q[1])) for Q in Qlist]
        if Detail: print("ALs: {}".format(ALs))
        # "transpose" this list of lists:
        ALeigs = [[[Q[0],ALs[i][j][0]] for i,Q in enumerate(Qlist)] for j in range(nnf)]
        if Detail: print("ALeigs: {}".format(ALeigs))
    else:
        ALeigs = [[] for _ in range(nnf)]

    Nko = (N,k,chi_number)
    if Detail: print("traces set = {}".format([1 if t else 0 for t in traces]))
    if Detail: print("ans set = {}".format([1 if a else 0 for a in ans]))
    Qx = PolynomialRing(QQ,'x')
    pari_nfs = [
        { 'Nko': Nko,
          'SB': SturmBound,
          'chipoly': chipoly,
          'dim': dims[i],
          'pari_newform': newforms[i],
          'poly': Qx.gen() if dims[i] == 1 else (pols[i] if dims[i] <= dmax else None),
          'best_poly': Qx.gen() if dims[i] == 1 else None,
          'ans': ans[i],
          'ALeigs': ALeigs[i],
          'traces': traces[i],
        }   for i in range(nnf)]
    if len(pari_nfs)>1:
        pari_nfs.sort(key=lambda f: f['traces'])
    t1=time.time()
    if Detail:
        print("{}: finished constructing GP newforms (time {:0.3f})".format(Nko,t1-t0))
    if d1 == dm:
        return pari_nfs

    # At this point we have everything we need, but the ans have not been optimized (or even made integral)
    nfs = [process_pari_nf_v1(pari_nfs[i], dmax, Detail) for i in range(d1,dm)]

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
        print("Total time for space {}: {:0.3f}".format(Nko,t4-t0))
    return [pari_nfs[i] for i in range(d1)] + nfs + [pari_nfs[i] for i in range(dm,nnf)]

def Newforms_v2(N, k, chi_number, dmax=20, nan=100, Detail=0):
    t0=time.time()
    G = pari(N).znstar(1)
    chi_dc = char_orbit_index_to_DC_number(N,chi_number)
    chi_gp = G.znconreylog(chi_dc)
    chi_order = ZZ(G.charorder(chi_gp))
    if Detail:
        print("Decomposing space {}:{}:{}".format(N,k,chi_number))
    NK = [N,k,[G,chi_gp]]
    pNK = pari(NK)
    if Detail>1:
        print("NK = {} (gp character = {})".format(NK,chi_gp))
    SturmBound = pNK.mfsturm()
    Snew = pNK.mfinit(0)
    total_dim = Snew.mfdim() # this is the relative dimension i.e. degree over Q(chi)
    # Get the character polynomial

    # Note that if the character order is 2*m with m odd then Pari uses the
    # m'th cyclotomic polynomial and not the 2m'th (e.g. for a
    # character of order 6 it uses t^2+t+1 and not t^2-t+1).

    chi_order_2 = chi_order//2 if chi_order%4==2 else chi_order
    chipoly = cyclotomic_polynomial(chi_order_2,'t')
    chi_degree = chipoly.degree()
    assert chi_degree==euler_phi(chi_order)==euler_phi(chi_order_2)
    t05=time.time()
    if Detail:
        print("Computed newspace {}:{}:{} in {:0.3f}, dimension={}*{}={}, now splitting into irreducible subspaces".format(N,k,chi_number, t05-t0, chi_degree,total_dim,chi_degree*total_dim))
        if Detail>1:
            print("Sturm bound = {}".format(SturmBound))
            print("character order = {}".format(chi_order))

    if total_dim==0:
        if Detail:
            print("The space {}:{}:{} is empty".format(N,k,chi_number))
        return []

    # First just compute Hecke matrices one at a time, to find a splitting operator
    def Hecke_op_iter():
        p=ZZ(1)
        while True:
            p = p.next_prime()
            # while p.divides(N):
            #     p=p.next_prime()
            #print("Computing T_{}".format(p))
            yield p, Snew.mfheckemat(p)

    Tp_iter = Hecke_op_iter()
    p, op = Tp_iter.next()
    s1=time.time()
    if Detail:
        print("testing T_{}".format(p))
    ok = is_semisimple_modular(op,chi_order_2)
    # f = op.charpoly()
    # ok = f.issquarefree()
    if ok:
        if Detail:
            print("Lucky first time: semisimple. Finding char poly")
        f = op.charpoly()
    ops=[(p,op)]
    while not ok:
        pi, opi = Tp_iter.next()
        if Detail:
            print("testing T_{}".format(pi))
        ok = is_semisimple_modular(op,chi_order_2)
        # f = opi.charpoly()
        # ok = f.issquarefree()
        if ok:
            if Detail:
                print("success using T_{}. Finding char poly".format(pi))
            op = opi
            f = op.charpoly()
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
                op = sum([ci*opj[1] for ci,opj in zip(co,ops)])
                ok = is_semisimple_modular(op,chi_order_2)
                # f=op.charpoly()
                # ok = f.issquarefree()
                if ok:
                    if Detail:
                        print("success using {}-combo of T_p for p in {}. Finding char poly".format(co,[opj[0] for opj in ops]))
                    f = op.charpoly()
                    break

    if not ok:
        raise RuntimeError("failed to find a 0,1-combination of Tp which is semisimple")
    ffac = f.factor()
    nnf = ffac.matsize()[0]
    gp_pols = pari_col1(ffac)
    pols = [pol for pol in gp_pols]
    reldims = [pol.poldegree() for pol in pols]
    dims = [d*chi_degree for d in reldims]
    # We'll need the coefficients an, if any newforms have dimension >1 and <=dmax.
    an_needed = [i for i,d in enumerate(dims) if d>1 and (dmax==0 or d<=dmax)]
    if Detail:
        print("Need to compute a_n for {} newforms: {}".format(len(an_needed), an_needed))

    s2=time.time()
    if Detail:
        print("Computed splitting in {:0.3f}, # newforms = {}".format(s2-s1,nnf))
        print("relative dims = {},  absolute dims = {}".format(reldims,dims))

    # Compute AL-matrices if character is trivial:
    if chi_order==1:
        Qlist = [(pr,pr**e) for pr,e in ZZ(N).factor()]
        ALs = [Snew.mfatkininit(Q[1])[1] for Q in Qlist]
        if Detail:
            print("AL-matrices:")
            for Q,AL in zip(Qlist,ALs):
                print("W_{}={}".format(Q[1],AL) )

    if nnf==1 and dims[0]>dmax and dmax>0:
        if Detail:
            print("Only one newform and dim={}, so use traceform to get traces".format(dims[0]))
        traces = pNK.mftraceform().mfcoefs(nan)
        if Detail>1:
            print("raw traces: {}".format(traces))
        if chi_degree>1:
            # This is faster than the more simple
            # traces = [c.trace() for c in traces]
            gptrace = pari_trace(chi_degree)
            traces = pari.apply(gptrace,traces)
            if Detail>1:
                print("traces to QQ: {}".format(traces))
        traces = gen_to_sage(traces)[1:]
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
        As = [(hi*(fi.gcdext(hi)[2])).subst(pari_x,op) for fi,hi in zip(pols,hs)]
        if Detail:
            print("Computed idempotent matrix decomposition")
        ims = [A.matimage() for A in As]
        U = pari.matconcat(ims)
        Uinv = U**(-1)
        if Detail:
            print("Computed U and U^-1")
        starts = [1+sum(d for d in reldims[:i]) for i in range(len(reldims))]
        stops = [sum(d for d in reldims[:i+1]) for i in range(len(reldims))]
        slicers = [pari_row_slice(r1,r2) for r1,r2 in zip(starts,stops)]
        ums = [slice(Uinv) for slice in slicers]
        imums = [imA*umA for imA,umA in zip(ims,ums)]
        s3=time.time()
        if Detail:
            print("Computed projectors in {:0.3f}".format(s3-s2))
            print("Starting to compute {} Hecke matrices T_n".format(nan))
        heckemats = Snew.mfheckemat(pari(range(1,nan+1)))
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
        gptrace = pari('c->if(type(c)=="t_POLMOD",trace(c),c*{})'.format(chi_degree))
        traces = [[gen_to_sage(gptrace(pari_trace_product(T,imum))) for T in heckemats] for imum in imums]
        s4=time.time()
        if Detail:
            print("Computed traces to Z in {:0.3f}".format(s4-s3))
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

            imsicol1 = pari_col1(ims[i])
            umsi = ums[i]
            ans[i] = [(umsi*(T*imsicol1)).Vec() for T in heckemats]
            if Detail:
                print("ans done")
                if Detail>1:
                    print("an: {}...".format(ans[i]))

            # Now compute the bases (of the relative Hecke field over
            # Q(chi) w.r.t which these coefficients are given.  Here
            # we use e1 because we picked the first column just now.

            B = ums[i]*op*ims[i]
            e1 = pari_e1(dr)
            cols = [e1]
            while len(cols)<dr:
                cols.append(B*cols[-1])
            W = pari.matconcat(cols)
            bases[i] = W.mattranspose()**(-1)
            if Detail>1:
                print("basis = {}".format(bases[i].lift()))

    # Compute AL-eigenvalues if character is trivial:
    if chi_order==1:
        ALeigs = [[
            [Q[0], gen_to_sage((umA*(AL*(pari_col1(imA))))[0])]
            for Q,AL in zip(Qlist,ALs)]
                  for umA,imA in zip(ums,ims)]
        if Detail>1: print("ALeigs: {}".format(ALeigs))
    else:
        ALeigs = [[] for _ in range(nnf)]

    Nko = (N,k,chi_number)
    #print("len(traces) = {}".format(len(traces)))
    #print("len(newforms) = {}".format(len(newforms)))
    #print("len(pols) = {}".format(len(pols)))
    #print("len(ans) = {}".format(len(ans)))
    #print("len(ALeigs) = {}".format(len(ALeigs)))

    pari_nfs = [
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
    #return pari_nfs

    t1=time.time()
    if Detail:
        print("{}: finished constructing pari newforms (time {:0.3f})".format(Nko,t1-t0))
    nfs = [process_pari_nf(nf, dmax, Detail) for nf in pari_nfs]
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
        print("Total time for space {}: {:0.3f}".format(Nko,t4-t0))
    return nfs

Newforms = Newforms_v1

def process_pari_nf(pari_nf, dmax=20, Detail=0):
    r"""
    Input is a dict with keys 'Nko' (N,k,chi_number), 'chipoly',  'SB' (Sturm bound), 'pari_newform',  'poly',  'ans',   'ALeigs', 'traces'

    Output adds 'traces' (unless already computed), and also 'eigdata' if 1<dimension<=dmax
    We do not yet use polredbest or optimize an coeffients

    NB This must be called on  each newform *before* the GP process associated with the data has been terminated.

    """
    Nko = pari_nf['Nko']
    chipoly = pari_nf['chipoly']
    poly = pari_nf['poly']
    SB = pari_nf['SB']
    ALeigs = pari_nf['ALeigs']
    traces = pari_nf['traces']
    assert traces # not None
    ans = pari_nf['ans']
    basis = pari_nf['basis']

    # initialize with data needing no more processing:

    newform = {'Nko': Nko, 'chipoly': chipoly, 'SB': SB, 'ALeigs':ALeigs, 'traces':traces}

    # Set the polynomial.  poly is the relative polynomial, in x (so
    # just x if the top degree is 1) with coefficients either integers
    # (if the bottom degree is 1) or polmods with modulus chipoly.
    #  rel_poly is in Qchi[x].

    Qx = PolynomialRing(QQ,'x')
    #pari_Qx_poly_to_sage = lambda f: Qx(gen_to_sage(f.Vecrev()))
    Qchi = NumberField(chipoly,'t')
    chi_degree = chipoly.degree()
    # NB the only reason for negating the chi_degree parameter here is to get around a bug in the Sage/pari interface
    pari_Qchi_to_sage = lambda elt: Qchi(gen_to_sage(elt.lift().Vecrev(chi_degree)))
    Qchi_x = PolynomialRing(Qchi,'x')
    pari_Qchix_poly_to_sage = lambda f: Qchi_x([pari_Qchi_to_sage(co) for co in f.Vecrev()])

    rel_poly = pari_Qchix_poly_to_sage(poly)
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
        ancs = [gen_to_sage(an) for an in ans]
        t1 = time.time()
        if Detail:
            print("time for converting an coeffs to QQ = {}".format(t1-t0))
            if Detail>1:
                print("Coefficient vectors of ans: {}".format(ancs))
        newform['poly'] = rel_poly
        # basis is a pari matrix over Q
        basis = gen_to_sage(basis)

        newform['eigdata'] = {
            'pol': rel_poly.list(),
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
        ancs = [gen_to_sage(an[0].lift().Vecrev(dim)) for an in ans] # list of lists of integers/rationals
        t1 = time.time()
        if Detail:
            print("time for converting an coeffs to QQ = {}".format(t1-t0))
            if Detail>1:
                print("Coefficient vectors of ans: {}".format(ancs))
        newform['poly'] = chipoly
        # basis is a 1x1 gp matrix over Qchi, so we want the power basis for Qchi: trivial
        basis = [[int(i==j) for j in range(dim)] for i in range(dim)]

        newform['eigdata'] = {
            'pol': chipoly.list(),
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
    newform['poly'] = abs_poly = Frel.absolute_polynomial()(Qx.gen())
    t1 = time.time()
    if Detail:
        print("absolute poly = {}".format(abs_poly))
        if Detail>1:
            print("Frel = {}".format(Frel))
            print("Time to construct Frel and find absolute poly = {}".format(t1-t0))
    Fabs = Frel.absolute_field('a')
    if Detail>1:
        print("Fabs = {}".format(Fabs))
    rel2abs = Fabs.structure()[1] # the isomorphism Frel --> Fabs
    z = rel2abs(Qchi.gen())
    zpow = [z**i for i in range(chi_degree)]
    # convert basis to a Sage list of lists of elements of Qchi:
    our_basis_coeffs = [[pari_Qchi_to_sage(basis[i,j]) for j in range(rel_degree)] for i in range(rel_degree)]
    #print("our basis coeffs: {} (parent {})".format(our_basis_coeffs, our_basis_coeffs[0][0].parent()))
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

    ancs = [[gen_to_sage(c.lift().Vecrev(chi_degree)) for c in an] for an in ans]
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

def process_pari_nf_v1(pari_nf, dmax=20, Detail=0):
    r"""
    Input is a dict with keys 'Nko' (N,k,chi_number), 'chipoly',  'SB' (Sturm bound), 'pari_newform',  'poly',  'ans',   'ALeigs', 'traces'

    Output adds 'traces' (unless already computed), and also 'eigdata' if 1<dimension<=dmax
    We do not yet use polredbest or optimize an coeffients
    """
    Nko = pari_nf['Nko']
    chipoly = pari_nf['chipoly']
    poly = pari_nf['poly']
    SB = pari_nf['SB']
    ALeigs = pari_nf['ALeigs']
    traces = pari_nf['traces']

    # initialize with data needing no more processing:

    newform = {'Nko': Nko, 'chipoly': chipoly, 'SB': SB, 'ALeigs':ALeigs, 'traces':traces}

    # Set the polynomial.  This is a polynomial in y, (just y if the
    # top degree is 1) with coefficients either integers (if the
    # bottom degree is 1) or polmods with modulus chipoly.  In all
    # cases rel_poly will be in Qchi[y].

    Qx = PolynomialRing(QQ,'x')
    #pari_Qx_poly_to_sage = lambda f: Qx(gen_to_sage(f.Vecrev()))
    Qchi = NumberField(chipoly,'t')
    chi_degree = chipoly.degree()
    # NB the only reason for negating the chi_degree parameter here is to get around a bug in the Sage/pari interface
    pari_Qchi_to_sage = lambda elt: Qchi(gen_to_sage(elt.lift().Vecrev(chi_degree)))
    Qchi_x = PolynomialRing(Qchi,'x')
    pari_Qchix_poly_to_sage = lambda f: Qchi_x([pari_Qchi_to_sage(co) for co in f.Vecrev()])

    rel_poly = pari_Qchix_poly_to_sage(poly)
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

    # the newform will have its 'traces' field set already if it is
    # the only newform in its (N,k,chi)-newspace.  Otherwise we will
    # have set its 'ans' field and now compute the traces from that.
    # The 'ans' field will be None if we don't need the an, which is
    # if (1) the dimension is greater than dmax and (2) the
    # (N,k,chi)-newspace is irreducible.

    ans = pari_nf['ans']
    if Detail>1: print("raw ans = {}".format(ans))

    # dimension 1 spaces: special case simpler traces, and no more to do:

    x = Qx.gen()
    if dim==1:  # e.g. (11,2,1)[0]
        #traces = gen_to_sage(ans)[1:]
        newform['poly'] = x
        if Detail>1: print("traces = {}".format(newform['traces']))
        return newform

    # All dimensions >1: traces

    if newform['traces']==None:
        traces = [abstrace(an,dim) for an in ans][1:]
        # fix up trace(a_1)
        traces[0]=dim
        if Detail>1: print("traces = {}".format(traces))
        newform['traces'] = traces

    # no more data required for non-small spaces:

    if not small:
        return newform

    if chi_degree==1 or rel_degree==1: # e.g. (13,4,1)[1] or (25,2,4)[0] respectively

        # field is not relative, ans are t_POLMOD modulo pari_pol in y
        # or t, so if we lift them and take their coefficient vector
        # we'll get the coordinates w.r.t. a power basis for the field
        # defined by either rel_poly or chipoly.

        t0=time.time()
        # for an in ans[:20]:
        #     print("an = {}".format(an))
        #     print("an.lift() = {}".format(an.lift()))
        #     print("an.lift().Vecrev(dim) = {}".format(an.lift().Vecrev(dim)))
        #     print("gen_to_sage(an.lift().Vecrev(dim)) = {}".format(gen_to_sage(an.lift().Vecrev(dim))))
        ancs = [gen_to_sage(an.lift().Vecrev(dim)) for an in ans][1:]
        t1 = time.time()
        if Detail:
            print("time for converting an coeffs to QQ = {}".format(t1-t0))
        basis = [[int(i==j) for j in range(dim)] for i in range(dim)]
        newform['poly'] = poly = Qx(rel_poly) if chi_degree==1 else Qx(chipoly)

        if Detail>1:
            print("Coefficient vectors of ans: {}".format(ancs))

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
        if Detail>1:
            print("Time to construct Frel and find absolute poly = {}".format(t1-t0))
    Fabs = Frel.absolute_field('a')
    rel2abs = Fabs.structure()[1] # the isomorphism Frel --> Fabs
    z = rel2abs(Qchi.gen())
    y = rel2abs(Frel.gen())
    zpow = [z**i for i in range(chi_degree)]
    ypow = [y**j for j in range(rel_degree)]
    basis = sum([[(zpowi*ypowj).list() for zpowi in zpow] for ypowj in ypow],[])
    t2 = time.time()
    if Detail>1:
        print("Time to construct Fabs and y,z in Fabs and basis matrix = {}".format(t2-t1))

    #  Get coordinates of the an.  After lifting twice these are
    #  polynomials in Q[t][y] so simply extracting coefficient vectors
    #  gives their coordinates in terms of the basis z^i*y^j where
    #  Qchi=Q(z) and F=Qchi(y).  To relate these to the power basis of
    #  Fabs we only need the change of basis matrix whose rows give
    #  the power basis coefficients of each z^i*y^j (in the right
    #  order).

    ancs = [[gen_to_sage(c.lift().Vecrev(chi_degree)) for c in a.lift().Vecrev(rel_degree)] for a in ans][1:]
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
    if dim>dmax and dmax>0:
        nf['best_poly'] = None
        return nf
    Qx = PolynomialRing(QQ,'x')
    pari_Qx_poly_to_sage = lambda f: Qx(gen_to_sage(f.Vecrev()))
    poly = Qx(nf['poly'].list())
    if Detail:
        print("non-best poly for {} is {}".format(Nko,poly))
    nf['best_poly'] = best_poly = polredbest_stable(poly)
    if Detail:
        print("best_poly for {} is {}".format(Nko,best_poly))

    # Now the real work starts
    Fold = NumberField(poly,'a')
    #print("Fold = {}".format(Fold))
    Fnew = NumberField(best_poly,'b')
    #print("Fnew = {}".format(Fnew))
    iso = Fold.is_isomorphic(Fnew,isomorphism_maps=True)[1][0] # we do not care which isomorphism
    #print("iso = {} of type {}".format(iso, type(iso)))
    iso = Fold.hom([iso(Fnew.gen())])
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
    if 1<dim and  (dim<=dmax or dmax==0):
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
    t0 = time.time()
    if Detail>1:
        print("Before LLL, coefficients:\n{}".format(C))
    # convert to actual matrices:
    d = len(B)
    nan = len(C)
    B=Matrix(B)
    C=Matrix(C)
    if debug:
        print("B has size {}".format(B.dimensions()))
        #print("B={}".format(B))
        print("C has size {}".format(C.dimensions()))
        #print("C={}".format(C))
        CB=C*B
    # Make integral:
    C1, den = C._clear_denom()
    B1 = B/den
    t1 = time.time()
    if Detail:
        print("Cleared denominator = {} in {:0.3f}".format(den,t1-t0))
    # Make primitive:
    if debug:
        print("C1 is in {}".format(C1.parent()))
        #print("C1 = {}".format(C1))
    C1 = pari(C1)
    # if debug:
    #     print("B1={} in {}".format(B1, B1.parent()))
    B1 = pari(B1)
    V1V2S  = C1.matsnf(1)
    t2 = time.time()
    V2 = V1V2S[1]
    S = pari_row_slice(nan-d+1,nan)(V1V2S[2])
    if Detail:
        print("Computed Smith form in {:0.3f}".format(t2-t1))
    if debug:
        print("V1V2S[2] = {}".format(V1V2S[2]))
        print("S = {}".format(S))
        print("About to invert matrix of size {}".format(V2.matsize()))
    C1 *= V2
    B1 = V2**(-1)*B1
    if debug:
        assert CB==C1*B1
    scales = [S[i,i] for i in range(d)]
    if not all(s==1 for s in scales):
        if Detail:
            print("scale factors {}".format(scales))
        C1 *= S**(-1)
        B1 = S*B1
        if debug:
            assert CB==C1*B1

    # LLL-reduce
    U = C1.qflll()
    t3 = time.time()
    if Detail:
        print("LLL done in {:0.3f}".format(t3-t2))
    if debug:
        assert U.matdet() in [1,-1]
    C1 *= U
    B1 = U**(-1)*B1
    if debug:
        assert CB==C1*B1
        print("found Bred, Cred")
    # Convert back to lists of lists
    Cred = [ci.list() for ci in C1.mattranspose()]
    Bred = [bi.list() for bi in B1.mattranspose()]
    if Detail>1:
        print("After LLL, coefficients:\n{}\nbasis={}".format(Cred,Bred))
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
    n = -1 # will increment for each (N,k,chi) in range, so we skip unless n%njobs==jobno
    failed_spaces = []
    for N in range(1,Nmax+1):
        kmin = max(2,(RR(Nk2min)/N).sqrt().ceil())
        kmax = (RR(Nk2max)/N).sqrt().floor()
        if kmin>kmax:
            continue
        level_info = "N = {}: ".format(N)
        level_info += "{} <=k<= {}".format(kmin,kmax)
        #level_info += "({} <=Nk^2<= {})".format(N*kmin**2,N*kmax**2)
        #screen.write(level_info)
        info_written=False
        nchars = NChars(N)
        for k in range(kmin, kmax+1):
            if not info_written:
                screen.write(level_info)
                info_written=True
            screen.write(" k={}:".format(k))
            screen.flush()
            nspaces+=1

            for i in range(nchars):
                n += 1
                if n%njobs!=jobno:
                    continue

                if i: screen.write(",")
                screen.write("{}".format(i+1))
                screen.flush()
                t0=time.time()
                try:
                    newforms = Newforms(N,k,i+1,dmax,nan, Detail)
                    t0=time.time()-t0
                    line = data_to_string(N,k,i+1,t0,newforms) + "\n"
                    if out:
                        out.write(line)
                        out.flush()
                    else:
                        screen.write('\n')
                        screen.write(line)
                except PariError, e:
                    t1=time.time()
                    print("\n*************************\nPariError {} on ({},{},{}) after {}s\n***********************".format(e,N,k,i+1,t1-t0))
                    failed_spaces.append((N,k,i+1))
        if info_written:
            screen.write('\n')
            screen.flush()
    if out:
        out.close()
    if failed_spaces:
        print("Completed apart from: {}".format(failed_spaces))
    #return nspaces

def OneSpace_v1(N, k, char_number, dmax=20, nan=100, filename=None, prefix="", Detail=0):
    append = True
    if filename==None:
        filename = "{}{}.{}.{}.txt".format(prefix,N, k, char_number)
        append = False
    t0=time.time()
    newforms = Newforms_v1(N,k,char_number,dmax,nan, Detail)
    t0=time.time()-t0
    line = data_to_string(N,k,char_number,t0,newforms) + "\n"
    if append:
        out = open(filename, 'a')
    else:
        out = open(filename, 'w')
    out.write(line)
    out.close()
    if Detail:
        print("{} newforms computed in {:0.3f}s.  Output written to {}".format(len(newforms),t0,filename))

def OneSpace_v2(N, k, char_number, dmax=20, nan=100, filename=None, prefix="", Detail=0):
    append = True
    if filename==None:
        filename = "{}{}.{}.{}.txt".format(prefix,N, k, char_number)
        append = False
    t0=time.time()
    newforms = Newforms_v2(N,k,char_number,dmax,nan, Detail)
    t0=time.time()-t0
    line = data_to_string(N,k,char_number,t0,newforms) + "\n"
    if append:
        out = open(filename, 'a')
    else:
        out = open(filename, 'w')
    out.write(line)
    out.close()
    if Detail:
        print("{} newforms computed in {:0.3f}s.  Output written to {}".format(len(newforms),t0,filename))

OneSpace = OneSpace_v1

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

def WeightOne_v1(filename, Nmin, Nmax, dmax, nan=100, njobs=1, jobno=0, Detail=0):
# Outputs N:k:i:time:dims:traces:polys with polys only for dims<=dmax
    out = open(filename, 'w') if filename else None
    screen = sys.stdout
    n = -1 # will increment for each (N,1,chi) in range, so we skip unless n%njobs==jobno
    for N in range(Nmin,Nmax+1):
        nch = NChars(N)
        screen.write("N = {}, {} characters: ".format(N,nch))
        for i in range(nch):
            n += 1
            if n%njobs!=jobno:
                continue
            screen.write(" (o={}) ".format(i+1))
            screen.flush()
            t0=time.time()
            newforms = Newforms_v1(N,1,i+1,dmax,nan, Detail)
            t0=time.time()-t0
            line = data_to_string(N,1,i+1,t0,newforms) + "\n"
            if out:
                out.write(line)
                out.flush()
            else:
                screen.write('\n')
                screen.write(line)
        screen.write('\n')
        screen.flush()
    if out:
        out.close()

def WeightOne_v2(filename, Nmin, Nmax, dmax, nan=100, njobs=1, jobno=0, Detail=0):
# Outputs N:k:i:time:dims:traces:polys with polys only for dims<=dmax
    out = open(filename, 'w') if filename else None
    screen = sys.stdout
    n = -1 # will increment for each (N,1,chi) in range, so we skip unless n%njobs==jobno
    for N in range(Nmin,Nmax+1):
        nch = NChars(N)
        screen.write("N = {}, {} characters: ".format(N,nch))
        for i in range(nch):
            n += 1
            if n%njobs!=jobno:
                continue
            screen.write(" (o={}) ".format(i+1))
            screen.flush()
            t0=time.time()
            newforms = Newforms_v2(N,1,i+1,dmax,nan, Detail)
            t0=time.time()-t0
            line = data_to_string(N,1,i+1,t0,newforms) + "\n"
            if out:
                out.write(line)
                out.flush()
            else:
                screen.write('\n')
                screen.write(line)
        screen.write('\n')
        screen.flush()
    if out:
        out.close()

WeightOne = WeightOne_v1

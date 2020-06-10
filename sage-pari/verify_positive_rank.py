"""
This code verifies that all classical modular forms in the LMFDB that appear to be of analytic 
rank 1 are actually provably of analytic rank 1 by verifying that the rank is positive. For self
dual forms of rank 2, this also verifies that the analytic rank is equal to 2 (by parity).
"""

import sys, os
try:
    # Make lmfdb available
    sys.path.append("/home/lmfdb/lmfdb") # for GCP
    sys.path.append(os.path.join(os.path.dirname(os.path.realpath(__file__)),"../lmfdb/"))
except NameError:
    pass
from lmfdb import db
from lmfdb.classical_modular_forms.web_newform import WebNewform
from sage.databases.cremona import cremona_letter_code
from dirichlet_conrey import DirichletGroup_conrey, DirichletCharacter_conrey

from sage.all import ModularSymbols, QQ, ZZ, PolynomialRing, cputime, oo, prime_range, gcd

def dirichlet_character_from_lmfdb_mf(data):
    G = DirichletGroup_conrey(data[u'level'])
    return DirichletCharacter_conrey(G,data[u'conrey_indexes'][0])

def modular_symbols_ambient_from_lmfdb_mf(data):
    chi = dirichlet_character_from_lmfdb_mf(data)
    return ModularSymbols(chi.sage_character(),data[u'weight'])

def windingelement_hecke_cutter_projected(data, extra_cutter_bound = None):
    "Creates winding element projected to the subspace where the hecke cutter condition of the data is satisfied"
    M = modular_symbols_ambient_from_lmfdb_mf(data)
    #dim = M.dimension()
    S = M.cuspidal_subspace()
    K = M.base_ring()
    R = PolynomialRing(K,"x")
    cutters = data[u'hecke_cutters']
    cutters_maxp = cutters[-1][0] if cutters else 1
    weight = data[u'weight']
    assert weight%2==0
    cuts_eisenstein = False
    winding_element = M.modular_symbol([weight//2-1,0,oo]).element()

    if extra_cutter_bound:
        N = data[u'level']
        wn = WebNewform(data)
        #qexp = qexp_as_nf_elt(wn,prec=extra_cutter_bound)
        for p in prime_range(cutters_maxp,extra_cutter_bound):
            if N%p ==0:
                continue
            cutters.append([p,qexp_as_nf_elt(wn)[p].minpoly().list()])

    for c in cutters:
        p = c[0]
        fM = M.hecke_polynomial(p)
        fS = S.hecke_polynomial(p)
        cutter = gcd(R(c[1]),fS)
        assert not cutter.is_constant()
        for cp,ce in cutter.factor():
            assert ce==1
            e = fM.valuation(cp)
            if fS.valuation(cp)==e:
                cuts_eisenstein = True
            winding_element = polynomial_matrix_apply(fM//cp**e,M.hecke_matrix(p),winding_element)
            if winding_element == 0:
                return winding_element
            #print(fS.valuation(cp),fM.valuation(cp),ce)

        assert cuts_eisenstein
    return winding_element


def polynomial_matrix_apply(f, M, v, rows=True):
    "let f be a polynomial M a matrix and v a vector this returns v*f(M)"
    d = f.degree()
    return sum(x * y for x, y in zip(f, M.iterates(v, d + 1, rows=rows)))


def qexp_as_nf_elt(self, prec=None):
    assert self.has_exact_qexp
    if prec is None:
        qexp = self.qexp
    else:
        qexp = self.qexp[:prec+1]
    if self.dim == 1:
        return [QQ(i[0]) for i in self.qexp]

    R = PolynomialRing(QQ,'x')
    K = QQ.extension(R(self.field_poly),'a')
    if self.hecke_ring_power_basis:
        return [K(c) for c in qexp]
    else:
        # need to add code to hande cyclotomic_generators
        assert self.hecke_ring_numerators,self.hecke_ring_denominators
        basis_data = zip(self.hecke_ring_numerators,self.hecke_ring_denominators)
        betas = [K([ZZ(c)/den for c in num]) for num, den in basis_data]
        return [sum(c*beta for c, beta in zip(coeffs, betas)) for coeffs in qexp]

def rank_is_positive(label, extra_cutter_bound=100):
    data = db.mf_newforms.lookup(label)
    if not data:
        print("cmf label %s not found in LMFDB!" % (label))
        assert data
    return windingelement_hecke_cutter_projected(data,extra_cutter_bound) == 0

def check_unproven_ranks(jobs=1,jobid=0,use_weak_bsd=False,skip_real_char=False):
    todo = list(db.mf_newforms.search({u'analytic_rank':{'$gt':int(1)},u'analytic_rank_proved':False}))
    todo2 = []; todo3 = []; todo4 = []
    cnt = 0; vcnt = 0
    for i in range(len(todo)):
        if i%jobs != jobid:
            continue
        start = cputime()
        data = todo[i]
        if skip_real_char and data[u"char_is_real"]:
            continue
        if use_weak_bsd and data[u'weight'] == 2 and data[u'dim'] == 1 and data[u'char_orbit_index'] == 1:
            ec_label = "%d.%s1"%(data[u'level'],cremona_letter_code(data[u'hecke_orbit']-1))
            r = db.ec_curves.lookup(ec_label)[u'rank']
            if data[u'analytic_rank'] != r:
                print("*** winding element is nonzero, positive analytic rank %d for newform %s appears to be wrong ***"%(data[u'rank'],data[u'label']))
                print(data[u'label'])
                todo2.append(data[u'label'])
            else:
                print("verified that analytic rank %d of newform %s matches Mordell-Weil rank of elliptic curve %s"%(data[u'analytic_rank'],data[u'label'],ec_label))
            continue
        print("Checking newform %s of dimension %d with analytic rank <= %d..."%(data[u'label'],data[u'dim'],data[u'analytic_rank']))
        w = windingelement_hecke_cutter_projected(data, extra_cutter_bound=100)
        if w != 0:
            print("*** winding element is nonzero, positive analytic rank %d for newform %s appears to be wrong ***"%(data[u'rank'],data[u'label']))
            print(data[u'label'])
            todo2.append(data[u'label'])
        else:
            if data[u'analytic_rank'] == 2 and data["is_self_dual"]:
                print("Verified analytic rank is 2.")
                vcnt += 1
            else:
                print("Verified analytic rank > 0")
                todo3.append(data[u'label'])
        print("Processed newform %s in %.3f CPU seconds"%(data[u'label'],cputime()-start))
        cnt += 1

    todo = list(db.mf_newforms.search({u'analytic_rank':int(1),u'is_self_dual':False,u'analytic_rank_proved':False}))
    for i in range(len(todo)):
        if i % jobs != jobid:
            continue
        start = cputime()
        data = todo[i]
        if skip_real_char and data[u"char_is_real"]:
            continue
        print("Checking non-self-dual newform %s of dimension %d with analytic rank <= %d..." % (data[u'label'], data[u'dim'], data[u'analytic_rank']))
        w = windingelement_hecke_cutter_projected(data, extra_cutter_bound=100)
        if w != 0:
            print("*** winding element is nonzero, positive analytic rank appears to be wrong ***")
            print(data[u'label'])
            todo4.append(data[u'label'])
        else:
            print("Verified analytic rank is 1.")
            vcnt += 1
        print("Processed newform %s in %.3f CPU seconds" % (data[u'label'], cputime() - start))
        cnt += 1

    print("Checked analytic ranks of %d newforms, of which %d were verified" % (cnt, vcnt))
    if todo2 or todo4:
        print("The following newforms appear to have the wrong analytic rank:")
        for r in todo2:
            print("    %s (claimed analytic rank %d)" % (r[u'lable'], r[u'analytic_rank']))
        for r in todo4:
            print("    %s (claimed analytic rank %d)" % (r[u'lable'], r[u'analytic_rank']))
    if todo3:
        print("The following newforms have positive but unverified analytic ranks:")
        for r in todo2:
            print("    %s (claimed analytic rank %d, proved nonzero)" % (r[u'lable'], r[u'analytic_rank']))

if __name__ == '__main__':
    print("running rank_is_positive(%r)" % sys.argv[1])
    result = rank_is_positive(sys.argv[1])
    print("result is", result)

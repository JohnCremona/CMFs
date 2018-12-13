"""
This code verifies that all classical modular forms in the LMFDB that appear to be of analytic 
rank 1 are actually provably of analytic rank 1. And additionally that all that appear to be of
analytic rank are >= 1 are actually of analytic rank >=1.

This uses the slow sage modular symbols code, but at the moment it runs just fine for all the needed
modular forms.
"""
from lmfdb.classical_modular_forms.web_newform import *
from lmfdb.db_backend import db

def dirichlet_character_from_lmfdb_mf(data):
    G = DirichletGroup_conrey(data[u'level'])
    return DirichletCharacter_conrey(G,data[u'char_labels'][0])

def modular_symbols_ambient_from_lmfdb_mf(data):
    chi = dirichlet_character_from_lmfdb_mf(data)
    return ModularSymbols(chi.sage_character(),data[u'weight'])

def windingelement_hecke_cutter_projected(data, extra_cutter_bound = None):
    "Creates winding element projected to the subspace where the hecke cutter condition of the data is satisfied"
    M = modular_symbols_ambient_from_lmfdb_mf(data)
    dim = M.dimension()
    S = M.cuspidal_subspace()
    K = M.base_ring()
    R = PolynomialRing(K,"x")
    cutters = data[u'hecke_cutters']
    weight = data[u'weight']
    assert weight%2==0
    cuts_eisenstein = False
    winding_element = M.modular_symbol([weight//2-1,0,oo]).element()

    if extra_cutter_bound:
        N = data['level']
        wn = WebNewform(data)
        qexp = qexp_as_nf_elt(wn,prec=extra_cutter_bound)
        for p in prime_range(data['hecke_cutters'][-1][0]+1,extra_cutter_bound):
            if N%p ==0:
                continue
            cutters.append([p,qexp_as_nf_elt(wn)[p].minpoly().list()])


    for c in cutters:
        p = c[0]
        print p
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
            #print fS.valuation(cp),fM.valuation(cp),ce

        assert cuts_eisenstein
    return winding_element

def polynomial_matrix_apply(f,M,v,rows=True):
    "let f be a polynomial M a matrix and v a vector this returns v*f(M)"
    d = f.degree()
    return sum(x*y for x,y in zip(f,M.iterates(v,d+1,rows=rows)))


def qexp_as_nf_elt(self,prec = None):
    if prec is None:
        qexp = self.qexp
    else:
        qexp = self.qexp[:prec+1]
    if self.dim == 1:
        return [QQ(i[0]) for i in self.qexp]

    R = PolynomialRing(QQ,'x')
    K = QQ.extension(R(self.field_poly),'a')
    basis_data = zip(self.hecke_ring_numerators,self.hecke_ring_denominators)
    betas = [K([ZZ(c)/den for c in num]) for num, den in basis_data]
    return [sum(c*beta for c, beta in zip(coeffs, betas)) for coeffs in qexp]


if __name__ == "__main__":
    todo = list(db.mf_newforms.search({u'analytic_rank':{'$gt':int(1)}}))
    todo2 = []
    for data in todo:
        print data[u'label']
        w = windingelement_hecke_cutter_projected(data, extra_cutter_bound = 50)
        if w!=0:
            print "warining: winding element is nonzero"
            print data[u'label']
            todo2.append(data[u'label'])

    assert len(todo2)==0

    todo = list(db.mf_newforms.search({u'analytic_rank':int(1),u'is_self_dual':{'$ne':int(1)}}))
    todo2 = []
    for data in todo:
        print data[u'label']
        w = windingelement_hecke_cutter_projected(data, extra_cutter_bound = 50)
        if w!=0:
            print "warining: winding element is nonzero"
            print data[u'label']
            todo2.append(data[u'label'])

    assert len(todo2)==0



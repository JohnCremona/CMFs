from sage.all import vector, CC, PolynomialRing, ZZ, NumberField
import os
os.chdir('/home/edgarcosta/lmfdb/')
from  lmfdb.db_backend import db
ZZx = PolynomialRing(ZZ, "x")
def convert_eigenvals_to_qexp(basis, eigenvals):
    qexp = [0]
    for i, ev in enumerate(eigenvals):
        if ev['n'] != i+1:
            raise ValueError("Missing eigenvalue")
        if 'an' in ev:
            an = sum(elt * basis[i] for i, elt in enumerate(ev['an']))
            qexp.append(an)
        else:
            raise ValueError("Missing eigenvalue")
    return qexp

for rowcc in db.mf_hecke_cc.search(
    {'embedding_root_real':None},
    projection=['an', 'hecke_orbit_code','id','lfunction_label']):
    row_embeddings =  {}
    hecke_orbit_code = rowcc['hecke_orbit_code']
    newform = db.mf_newforms.lucky({'hecke_orbit_code':hecke_orbit_code})
    if newform['dim'] == 1:
        row_embeddings['embedding_root_imag'] = 0
        row_embeddings['embedding_root_real'] = 0
    else:
        print rowcc['lfunction_label']
        an_cc = map(lambda x: CC(x[0], x[1]), rowcc.pop('an'))
        HF = NumberField(ZZx(newform['field_poly']), "v")
        numerators =  newform['hecke_ring_numerators']
        denominators = newform['hecke_ring_denominators']
        betas = [HF(elt)/denominators[i] for i, elt in enumerate(numerators)]

        row_hecke_nf = db.mf_hecke_nf.lucky({'hecke_orbit_code':hecke_orbit_code})
        embeddings = HF.complex_embeddings()
        an_nf = list(db.mf_hecke_nf.search({'hecke_orbit_code':hecke_orbit_code}, ['n','an'], sort=['n']))
        betas_embedded = [map(elt, betas) for elt in embeddings]
        qexp = [convert_eigenvals_to_qexp(elt, an_nf) for elt in betas_embedded]
        min_len = min(len(an_cc), len(qexp[0]))
        an_cc = vector(CC, an_cc[:min_len])
        qexp_diff = [ (vector(CC, elt[:min_len]) - an_cc).norm() for elt in qexp ]
        min_diff = min(qexp_diff)

        #assuring that is something close to zero
        assert min_diff < 1e-6
        for i, elt in enumerate(qexp_diff):
            if elt == min_diff:
                row_embeddings['embedding_root_imag'] = embeddings[i](HF.gen()).real()
                row_embeddings['embedding_root_real'] = embeddings[i](HF.gen()).imag()
            else:
                #assuring that no other value is close to it
                assert elt*1e-6 > min_diff
    assert len(row_embeddings) == 2
    db.mf_hecke_cc.upsert({'id': rowcc['id']}, row_embeddings)

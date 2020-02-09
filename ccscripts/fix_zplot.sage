# code to fix the Z-plot of non-self dual L-functions with positive rank

from lmfdb.backend import db, SQL

def fix_zplot_sign_orbit(label):
    print label
    origin = 'ModularForm/GL2/Q/holomorphic/' + label.replace('.','/')
    proj = ['id','z1','Lhash','plot_delta','plot_values','conjugate', 'origin']
    Ls =  list(db.lfunc_lfunctions.search({'origin':{'$startswith': origin + '/'}},proj))
    Ls_dict = {ell['Lhash'] : ell for ell in Ls}
    pairs = Set([tuple(sorted([ell['Lhash'], ell['conjugate']])) for ell in Ls])
    assert pairs.cardinality()*2 == len(Ls)
    sign = 1
    for pair in pairs:
        pair = list(pair)
        L0 = Ls_dict[pair[0]]
        L1 = Ls_dict[pair[1]]
        LV0 = [L0['plot_values'][i] for i in range(1, floor(L0['z1']/L0['plot_delta']) + 1)]
        LV1 = [L1['plot_values'][i] for i in range(1, floor(L1['z1']/L1['plot_delta']) + 1)]
        LV0r = [min(LV0), max(LV0)]
        LV1r = [min(LV1), max(LV1)]
        # print LV0r, LV1r
        # the plot hasn't changed sign
        assert LV0r[0] * LV0r[1] > 0
        assert LV1r[0] * LV1r[1] > 0
        if LV0r[0] * LV1r[0] > 0:
            # they have the same sign! we need to fix one of them
            sign *= -1
            fixLV1 = [-1*elt for elt in L1['plot_values']]
            print L1['origin']
            db.lfunc_lfunctions.update({'id':L1['id']},{'plot_values':fixLV1}, restat = False)
    if sign == -1:
        # also need to fix the orbit
        L = db.lfunc_lfunctions.lucky({'origin':origin},['id','plot_values'])
        print origin
        fixLV = [-1*elt for elt in L['plot_values']]
        db.lfunc_lfunctions.update({'id':L1['id']},{'plot_values':fixLV1}, restat = False)
        

import os, sys
os.chdir('/home/edgarcosta/lmfdb/')
sys.path.append('/home/edgarcosta/lmfdb/')
from  lmfdb.db_backend import db




def upsert_trace_hash(id_number):
    newform = db.mf_newforms.lucky({'id':id_number}, projection=['label','trace_hash','dim'])
    if newform is None:
        return
    if newform.get('trace_hash',None) is None:
        assert newform['dim'] > 20
        return
    base_url = "ModularForm/GL2/Q/holomorphic/" + newform['label'].replace(".","/")
    trace_hash = newform['trace_hash']
    Lhash = db.lfunc_instances.lucky({'url': base_url}, projection='Lhash')
    if Lhash is None:
        assert newform['dim'] > 80
        return
    assert Lhash is not None, 'url = %s' % base_url
    db.lfunc_lfunctions.upsert({'Lhash': Lhash}, {'trace_hash' : trace_hash})

import sys
if len(sys.argv) == 3:
    bound = db.mf_newforms.max_id()
    k = int(sys.argv[1])
    start = int(sys.argv[2])
    assert k > start
    ids = list(range(start, bound + 1, k))
    for i in ids:
        upsert_trace_hash(i)

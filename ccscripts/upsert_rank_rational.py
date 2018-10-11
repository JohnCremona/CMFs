import os, sys
os.chdir('/home/edgarcosta/lmfdb/')
sys.path.append('/home/edgarcosta/lmfdb/')
from  lmfdb.db_backend import db




def upsert_rank(id_number):
    newform = db.mf_newforms.lucky({'id':id_number}, projection=['label','trace_hash'])
    if newform is None:
        return
    base_url = "ModularForm/GL2/Q/holomorphic/" + newform['label'].replace(".","/")
    trace_hash = newform['trace_hash']
    rank = db.lfunc_lfunctions.lucky({'origin' : base_url}, projection='order_of_vanishing')
    assert rank is not None
    print newform['label'], rank
    db.mf_newforms.update({'id': id_number}, {'analytic_rank' : rank})

import sys
if len(sys.argv) == 3:
    bound = db.mf_newforms.max_id()
    k = int(sys.argv[1])
    start = int(sys.argv[2])
    assert k > start
    ids = list(range(start, bound + 1, k))
    for i in ids:
        upsert_rank(i)

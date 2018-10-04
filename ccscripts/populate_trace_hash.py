import os, sys
os.chdir('/home/edgarcosta/lmfdb/')
sys.path.append('/home/edgarcosta/lmfdb/')
from  lmfdb.db_backend import db

def upsert_hash(id_number, skip = False):
    row = db.lfunc_lfunctions.lucky({'id':id_number}, projection = ['id', 'Lhash','trace_hash','origin'])
    if skip and 'trace_hash' in row:
        return
    trace_hash = int(row['Lhash'])
    assert trace_hash < 2**61
    assert "Genus2Curve/Q/" in row['origin'] or "EllipticCurve/Q/" in row['origin']
    db.lfunc_lfunctions.upsert({'id': row['id']}, {'trace_hash':trace_hash})

import sys
if len(sys.argv) == 3:
    mod = int(sys.argv[1])
    c = int(sys.argv[2])
    for key in ['G2Q','Cremona']:
        for i in db.lfunc_lfunctions.search({'load_key':key}, projection='id'):
            if (i % mod) == c:
                upsert_hash(i)


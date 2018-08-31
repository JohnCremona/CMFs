import sqlite3
import os
import sys
import struct

from dirichlet_conrey import *

def CBFlistcmp(L1, L2):
    for (z1, z2) in zip(L1, L2):
        x1, y1 = z1.real(), z1.imag()
        x2, y2 = z2.real(), z2.imag()
        if y1 < y2:
            return -1r
        elif y1 > y2:
            return 1r

    for (z1, z2) in zip(L1, L2):
        x1, y1 = z1.real(), z1.imag()
        x2, y2 = z2.real(), z2.imag()
        if x1 < x2:
            return -1r
        elif x1 > x2:
            return 1r

    return 0r

def CBFcmp(z1, z2):
    x1, y1 = z1.real(), z1.imag()
    x2, y2 = z2.real(), z2.imag()

    if x1 < x2:
        return -1
    elif x1 > x2:
        return 1
    elif y1 < y2:
        return -1
    elif y2 < y1:
        return 1

    return 0


MF_PREC_EXACT = 2147483647

def extend_multiplicatively(Z):
    for pp in prime_powers(len(Z)-1):
        for k in range(1, (len(Z) - 1)//pp + 1):
            if gcd(k, pp) == 1:
                Z[pp*k] = Z[pp]*Z[k]

def read_gmp_int(buf, offset):
    length = struct.unpack_from('>i', buf, offset)[0]
    bytes_read = 4
    sign = 1
    if length < 0:
        sign = -1
        length = -length
    if length > 10000: #something has probably gone wrong
        return
    limb_fmt = '{}B'.format(length)
    data = struct.unpack_from(limb_fmt, buf, offset + bytes_read)
    bytes_read = bytes_read + struct.calcsize(limb_fmt)
    number = sign*sum((x*2**(8*k) for (k,x) in enumerate(reversed(data))))
    return number, bytes_read

def read_orbit(orbitblob):
    A = struct.unpack_from('i'*(len(orbitblob)/4r), orbitblob)
    return [ (A[2*i], A[2*i+1]) for i in range(len(A)/2r) ]

#inpath = sys.argv[1]
#mfdbpath = sys.argv[2]

level = sys.argv[1]
weight = sys.argv[2]


base_path = "/scratch/home/bober"
polyinfile = os.path.join(base_path, 'polydb/{}.{}.polydb'.format(level, weight))
mfdbinfile = os.path.join(base_path, 'mfdb/{}.{}.mfdb'.format(level, weight))
Ldbinfile = os.path.join(base_path, 'mfldb/{}.{}.mfldb'.format(level, weight))

notfound = False

if not os.path.exists(polyinfile):
    print '{} not found'.format(polyinfile)
    notfound = True
if not os.path.exists(mfdbinfile):
    print '{} not found'.format(mfdbinfile)
    notfound = True
if not os.path.exists(Ldbinfile):
    print '{} not found'.format(Ldbinfile)
    notfound = True

if notfound:
    sys.exit(1)

level = int(level)
weight = int(weight)

#level_list = set()
#level_weight_list = []
#for dirpath, dirnames, filenames in os.walk(inpath):
#    for filename in filenames:
#        if not filename.endswith('.polydb'):
#            continue
#        level, weight, _ = filename.split('.')
#        level = int(level)
#        weight = int(weight)
#        level_weight_list.append( (level, weight, os.path.join(dirpath, filename)) )
#        level_list.add(level)
#
#level_list = sorted(level_list)
orbit_labels = {}
G = DirichletGroup_conrey(level)
orbits = G._galois_orbits()
for k, orbit in enumerate(orbits):
    for chi in orbit:
        orbit_labels[chi] = k + 1

degree_lists = {}
traces_lists = {}

CCC = ComplexBallField(2000)
RRR = RealIntervalField(2000)
db = sqlite3.connect(polyinfile)
db.row_factory = sqlite3.Row
'''
expected schema:
CREATE TABLE heckepolys (level INTEGER,
                         weight INTEGER,
                         chi INTEGER,
                         whatevernumber INTEGER,
                         labelnumber    INTEGER,
                         operator       BLOB,
                         degree         INTEGER,
                         mforbit        BLOB,
                         polynomial     BLOB);
'''

mfdb = sqlite3.connect(os.path.join(mfdbinfile))
mfdb.row_factory = sqlite3.Row

'''
expected schema:
    CREATE TABLE modforms (level INTEGER, weight INTEGER, chi INTEGER, orbit INTEGER, j INTEGER,
        prec INTEGER, exponent INTEGER, ncoeffs INTEGER, coefficients BLOB)
'''
coeffs = {}

for result in mfdb.execute('SELECT prec, exponent, ncoeffs, coefficients, chi, j FROM modforms WHERE level={} AND weight={};'.format(level, weight)):
    chi = result['chi']

    is_trivial = False
    is_quadratic = False
    if chi == 1:
        is_trivial = True
    elif (chi*chi) % level == 1:
        is_quadratic = True

    j = result['j']
    offset = 0
    coeffblob = result['coefficients']
    exponent = result['exponent']
    prec = result['prec']
    #print prec, exponent
    _coeffs = [CCC(0)] * 101
    #for k in range(35): # number of prime powers < 100
    for pp in prime_powers(100):
        z, bytes_read = read_gmp_int(coeffblob, offset)
        #print z
        offset = offset + bytes_read
        real_part = CCC(z*2^exponent)
        if prec != MF_PREC_EXACT:
            real_part = real_part.add_error(2^prec)
        imag_part = 0
        if not is_trivial:
            z, bytes_read = read_gmp_int(coeffblob, offset)
            offset = offset + bytes_read
            imag_part = CCC(I*z*2^exponent)
            if prec != MF_PREC_EXACT:
                imag_part = imag_part.add_error(2^prec)
        z = real_part + imag_part
        _coeffs[pp] = z
        #if not is_trivial and not is_quadratic:            # just for the moment...
        #    z = 2*real_part
        #traces[k] += z
    #print coeffs
    _coeffs[1] = CCC(1)
    extend_multiplicatively(_coeffs)
    coeffs[(chi, j)] = _coeffs
    chibar = inverse_mod(chi, level)
    if chibar > chi:
        coeffs[(chibar, j)] = [z.conjugate() for z in _coeffs]

#mforbits = {}

for result in db.execute('SELECT level, weight, chi, whatevernumber, labelnumber, degree, mforbit from heckepolys;'):
    level = result['level']
    weight = result['weight']
    chi = result['chi']
    original_chi = chi

    if (level, weight, chi) not in degree_lists:
        degree_lists[(level, weight, chi)] = []
        traces_lists[(level, weight, chi)] = []
    degree_lists[(level, weight, chi)].append(result['degree'])

    whatever = result['whatevernumber']
    label = result['labelnumber']
    degree = result['degree']
    mforbit = read_orbit(result['mforbit'])
    #mforbits[original_chi] = mforbit
    #print level, weight, chi, whatever, label, degree, mforbit

    is_trivial = False
    is_quadratic = False
    if chi == 1:
        is_trivial = True
    elif (chi*chi) % level == 1:
        is_quadratic = True

    traces = [RRR(0)] * 101
    for chi, j in mforbit:
        #if inverse_mod(chi, level) < chi:
        #    continue
        for k, z in enumerate(coeffs[(chi, j)]):
            traces[k] += RRR(z.real())
            #if not is_trivial and not is_quadratic:
            #    traces[k] += RRR(z.real())

    traces = [z.unique_integer() for z in traces]
    traces_lists[(level, weight, original_chi)].append((traces[1:], mforbit))
Ldb = sqlite3.connect(os.path.join(Ldbinfile))
Ldb.row_factory = sqlite3.Row

'''
expected schema:
CREATE TABLE modformLfunctions
   (level     INTEGER,
    weight     INTEGER,
    chi        INTEGER,
    orbit      INTEGER,
    j          INTEGER,
    rank       INTEGER,
    rankverified INTEGER,
    signarg    REAL
    gamma1     REAL,
    gamma2     REAL,
    gamma3     REAL,
    zeroprec   INTEGER,
    nzeros     INTEGER,
    zeros      BLOB,
    valuesdelta         REAL,
    nvalues             INTEGER,
    Lvalues             BLOB);
'''

zeros = {}
plots = {}
Ldbresults = {}
for result in Ldb.execute('SELECT level, weight, chi, j, rank, zeroprec, nzeros, zeros, valuesdelta, nvalues, Lvalues, signarg from modformLfunctions'):
    nzeros = result['nzeros']
    prec = result['zeroprec']
    chi = result['chi']
    j = result['j']
    #print result['level'], result['weight'], chi, j
    _zeros = []
    offset = 0
    for k in range(nzeros):
        nlimbs = struct.unpack_from(">I", result['zeros'], offset)[0]
        offset = offset + 4
        zdata = struct.unpack_from("B" * nlimbs, result['zeros'], offset)
        offset = offset + nlimbs
        z = sum( [x * 2**(8*k) for (k, x) in enumerate(reversed(zdata))] )
        _zeros.append(z)
    zeros[(chi,j)] = _zeros
    Ldbresults[(chi,j)] = result

'''
for level, weight, chi in sorted(degree_lists.keys()):
    toprint = '{}:{}:{}:[{}]:[{}]'.format(level, weight, orbit_labels[chi], sorted(degree_lists[(level, weight, chi)]), sorted(traces_lists[(level, weight, chi)]))
    print ''.join(toprint.split())
    for chi2, j in mforbits[chi]:
        print chi2, j, zeros[(chi2, j)]
'''

def convertbase26(j):
    if j == 0:
        return 'a'
    else:
        return "".join([chr(ord('a') + i) for i in reversed(ZZ(j).digits(base=26))])
def convert_label(label_str):
    N, k, chi, a, n =  map(int, label_str.split("."))
    a = convertbase26(a)
    return a, n

labels = {}
conjugates = {}
selfduals = {}


for level, weight, originalchi in sorted(degree_lists.keys()):
    #toprint = '{}:{}:{}:{}'.format(level, weight, orbit_labels[originalchi], sorted(degree_lists[(level, weight, originalchi)]))
    #print ''.join(toprint.split())
    for mforbitlabel, (traces, mforbit) in enumerate(sorted(traces_lists[(level, weight, originalchi)])):
        selfdual = False
        if originalchi == 1:
            selfdual = True
        if (originalchi*originalchi) % level == 1:
            Z = coeffs[mforbit[0]]
            selfdual = True
            for z in Z:
                if not z.imag().contains_zero():
                    selfdual = False
        #if selfdual:
        #    print '*',
        #print mforbit, traces
        chi_list = sorted(set( chi for (chi, j) in mforbit))
        for chi in chi_list:
            j_list = [j for (_, j) in mforbit if _ == chi]
            chibar = inverse_mod(chi, level)
            d = len(j_list)
            coeffs_list = [(chi, j, coeffs[(chi,j)]) for j in j_list]
            coeffs_list.sort(cmp=CBFlistcmp, key = lambda z : z[-1])
            for k, _coeffs in enumerate(coeffs_list):
                j = _coeffs[1]
                label = '{}.{}.{}.{}.{}'.format(level, weight, chi, mforbitlabel, k+1)
                if not selfdual:
                    conjugate = '{}.{}.{}.{}.{}'.format(level, weight, chibar, mforbitlabel, d - k)
                else:
                    conjugate = label
                sa, sn = convert_label(label)
                converted_label = (chi, sa, sn)
                labels[(chi, j)] = converted_label
                selfduals[converted_label] = selfdual
                ca, cn = convert_label(conjugate)
                conjugates[converted_label] = (chi, ca, cn)

## SATAKE
from dirichlet_conrey import DirichletGroup_conrey, DirichletCharacter_conrey
from sage.all import prime_range, pi

def satake(coeffs, level, weight, chi):
    """
    - ``coeffs`` -- a list of Dirichlet coefficients, as elements of CCC
    - ``level`` -- the level N
    - ``weight`` -- the weight k
    - ``chi`` -- the index of the Dirichlet character in the Conrey labeling
    """
    G = DirichletGroup_conrey(level, CCC)
    char = DirichletCharacter_conrey(G, chi)
    satakes = []
    for p in prime_range(1000):
        if p.divides(level):
            continue
        charval = CCC(2*char.logvalue(p)).exppii()
        b = coeffs[p]
        c = p**(weight-1)*charval
        alpha = (-b + (b**2 - 4*c).sqrt())/2
        theta = alpha.arg() / CCC(2*pi)
        satakes.append([p, float(theta.mid())])
    return satakes




####################
# postgres stuff
###################


default_type = 'CMF'

constant_lf = {
        'primitive' : 't', # True
        'conductor' : level,
        'load_key' : 'CMFs-workshop',
        'motivic_weight': weight - 1,
        'types': str([default_type]).replace("'","\""),
        'symmetry_type': '\N',
        'group' : 'GL2',
        'degree' : 2,
        'st_group' : '\N',
        'selfdual': '\N',
        'analytic_normalization': float(weight - 1)/2,
        'euler_factors': '\N',
        'precision': '\N',
        'bad_lfactors': '\N',
        'algebraic': 't',
        'coeff_info': '\N',
        'credit' : '\N',
        'values': '\N', # no special values at the moment
        'gamma_factors': [[], [0]],
        'coefficient_field': '\N', # the label of the Hecke field, we set as \N as start
        'dirichlet_coefficients' : '\N' # we already store a2 .. a10
        }




schema_lf = [
        'load_key', # 'CMFs'
        'origin', # ModularForm/GL2/Q/holomorphic/N/k/chi/a/n
        'primitive', # True
        'conductor', # N
        'central_character', # N.chi
        'self_dual',  # boolean, Bober tells me
        'motivic_weight', # k - 1
        'conjugate', # Bober tells me
        'types', # ['MF']
        'Lhash', # first zero: str(<first zero of L_0> * 2^100).round())
        'symmetry_type', # 'unitary' or 'orthogonal' or 'symplectic'  FIXME: delete?
        'group', # GL2
        'degree', # 2
        'st_group', # unkown for the moment
        'plot_delta', # numeric,
        'selfdual', # to be removed
        'analytic_normalization', # (k - 1)/2<D-f>
        'euler_factors', # Null in this case
        'z1', #first zero
        'z2', #2nd zero
        'z3', #3rd zero
        'precision', # this is only used for mass forms, might mean the precision of the eigenvalue in that case
        'accuracy', # bit accuracy (after the decimal point) of the nontrivial zeros
        'order_of_vanishing', # int
        'bad_lfactors', # Null for the moment
        'sign_arg', # muti valued denoting the angle
        'plot_values', # list of doubles
        'algebraic', # True
        'coeff_info', # ???? ,
        'leading_term', # WARNING is text
        'root_number', # WARNING text
        'positive_zeros', #list of doubles
        'credit', # empty string
        'gamma_factors', # jsonb,
        'values', # special values, format???
        'dirichlet_coefficients', # the ap traces as algebraic numbers
        'coefficient_field', # the label of the Hecke field
        ]
for i in range(2,11):
    constant_lf['A' + str(i)] = '\N'
    schema_lf.append('A'+ str(i))
    schema_lf.append('a' + str(i))

schema_lf_dict = dict([ (key, i) for i, key in enumerate(schema_lf)])

schema_lf_types = {u'A10': u'numeric',
 u'A2': u'numeric',
 u'A3': u'numeric',
 u'A4': u'numeric',
 u'A5': u'numeric',
 u'A6': u'numeric',
 u'A7': u'numeric',
 u'A8': u'numeric',
 u'A9': u'numeric',
 u'Lhash': u'text',
 u'a10': u'jsonb',
 u'a2': u'jsonb',
 u'a3': u'jsonb',
 u'a4': u'jsonb',
 u'a5': u'jsonb',
 u'a6': u'jsonb',
 u'a7': u'jsonb',
 u'a8': u'jsonb',
 u'a9': u'jsonb',
 u'accuracy': u'smallint',
 u'algebraic': u'boolean',
 u'analytic_normalization': u'numeric',
 u'bad_lfactors': u'jsonb',
 u'central_character': u'text',
 u'coeff_info': u'jsonb',
 u'coefficient_field': u'text',
 u'conductor': u'bigint',
 u'conjugate': u'text',
 u'credit': u'text',
 u'degree': u'smallint',
 u'dirichlet_coefficients': u'jsonb',
 u'euler_factors': u'jsonb',
 u'gamma_factors': u'jsonb',
 u'group': u'text',
 u'id': u'bigint',
 u'leading_term': u'text',
 u'load_key': u'text',
 u'motivic_weight': u'smallint',
 u'order_of_vanishing': u'smallint',
 u'origin': u'text',
 u'plot_delta': u'numeric',
 u'plot_values': u'jsonb',
 u'positive_zeros': u'jsonb',
 u'precision': u'smallint',
 u'primitive': u'boolean',
 u'root_number': u'text',
 u'self_dual': u'boolean',
 u'selfdual': u'boolean',
 u'sign_arg': u'numeric',
 u'st_group': u'text',
 u'symmetry_type': u'text',
 u'types': u'jsonb',
 u'values': u'jsonb',
 u'z1': u'numeric',
 u'z2': u'numeric',
 u'z3': u'numeric'}

schema_lf_types.pop('id')



for key in schema_lf_types.keys():
    assert key in schema_lf
for key in schema_lf:
    assert key in schema_lf_types, '%s not in schema_lf_types' % key

schema_instances = ['url', 'Lhash', 'type']

schema_instances_types = {u'Lhash': u'text', u'id': u'bigint', u'type': u'text', u'url': u'text'}
schema_instances_types.pop('id')


def origin(chi, a, n):
    return "ModularForm/GL2/Q/holomorphic/%d/%d/%d/%s/%d" % (level, weight, chi, a, n)

def label(chi,j):
    return labels[(chi,j)]





def self_dual(chi, a, n):
    return selfduals[(chi, a, n)]



Lhashes = {}
rows = {}

def populate_row(Ldbrow):
    row = dict(constant_lf)
    chi = int(Ldbrow['chi'])
    j = int(Ldbrow['j'])
    _, a, n = label(chi,j)

    row['order_of_vanishing'] = int(Ldbrow['rank'])
    zeros_as_int = zeros[(chi,j)][row['order_of_vanishing']:]
    prec = row['accuracy'] = Ldbrow['zeroprec']
    row['positive_zeros'] = [float(z/2**prec) for z in zeros_as_int]
    row['origin'] = origin(chi, a, n)
    row['central_character'] = "%s.%s" % (level, chi)
    row['self_dual'] = self_dual(chi, a, n)
    row['conjugate'] = None
    row['Lhash'] = str(zeros_as_int[0] * 2**(100-prec).round())
    if prec < 100:
        row['Lhash'] = '_' + row['Lhash']
    global Lhashes
    Lhashes[(chi, a, n)] = row['Lhash']
    row['sign_arg'] = float(Ldbrow['signarg']/(2*pi))
    for i in range(0,3):
        row['z' + str(i + 1)] = RealNumber(str(zeros_as_int[i]) + ".")/2**prec

    row['plot_delta'] = Ldbrow['valuesdelta']
    row['plot_values'] = list(struct.unpack('{}d'.format(len(Ldbrow['Lvalues'])/8), Ldbrow['Lvalues']))



    row['leading_term'] = '\N'
    row['root_number'] = str(CDF(exp(2*pi*I*row['sign_arg'])))
    #row['dirichlet_coefficients'] = [None] * 10
    for i, ai in enumerate(coeffs[(chi, j)][2:12]):
        ai = CDF(ai)
        ai_jsonb = [ai.real_part(), ai.imag_part()]
        if i + 2 <= 10:
            row['a' + str(i+2)] = ai_jsonb
        #row['dirichlet_coefficients'][i] = ai_jsonb



    for key in schema_lf:
        assert key in row, "%s not in row = %s" % (key, row)
    assert len(row) == len(schema_lf), "%s != %s" % (len(row) , len(schema_lf))

    #rewrite row as a list
    global rows
    rows[(chi, a, n)] = [row[key] for key in schema_lf]

def populate_rows():
    for key, row in Ldbresults.iteritems():
        populate_row(row)


def populate_conjugates():
#    print Lhashes.keys()
    for key, row in rows.iteritems():
#        print "key = %s" % (key,)
        row[schema_lf_dict['conjugate']] = Lhashes[conjugates[key]]


def write_header(lfunctions_filename, instances_filename):
    str_parsing_lf = '\t'.join(['%s'] * len(schema_lf)) + '\n'
    str_parsing_instances = '\t'.join(['%s'] * len(schema_instances)) + '\n'
    if not os.path.exists(lfunctions_filename):
        with open(lfunctions_filename,"w") as F:
            F.write(str_parsing_lf % tuple(schema_lf))
            F.write(str_parsing_lf % tuple([schema_lf_types[key] for key in schema_lf]))
            F.write("\n")

    if not os.path.exists(instances_filename):
        with open(instances_filename, "w") as F:
            F.write(str_parsing_instances % tuple(schema_instances))
            F.write(str_parsing_instances % tuple([schema_instances_types[key] for key in schema_instances]))
            F.write("\n")


# the function below assumes this order
assert schema_instances == ['url', 'Lhash', 'type']
ord_origin = schema_lf_dict['origin']
ord_Lhash = schema_lf_dict['Lhash']

def tuple_instance(row):
    return (row[ord_origin], row[ord_Lhash], default_type)

def export_rows(lfunctions_filename, instances_filename):
    write_header(lfunctions_filename, instances_filename)
    str_parsing_lf = '\t'.join(['%s'] * len(schema_lf)) + '\n'
    str_parsing_instances = '\t'.join(['%s'] * len(schema_instances)) + '\n'

    with open(lfunctions_filename, 'a') as LF:
        with open(instances_filename, 'a') as IF:
            for key, row in rows.iteritems():
                LF.write(str_parsing_lf % tuple(row))
                IF.write(str_parsing_instances % tuple_instance(row))


populate_rows()
populate_conjugates()
export_rows('/scratch/importing/CMF_Lfunctions.txt','/scratch/importing/CMF_instances.txt')

from sage.all import ComplexIntervalField, RealNumber, ZZ, CDF, prime_pi, prime_divisors, ComplexBallField, RealIntervalField,  QQ, prime_powers, PowerSeriesRing, PolynomialRing, prod, spline, srange, gcd, primes_first_n, exp, pi, I, next_prime, Infinity, RR
import os, sys, json
from dirichlet_conrey import DirichletGroup_conrey, DirichletCharacter_conrey

# 265 = 80 digits
default_prec = 300
CCC = ComplexBallField(default_prec)
RRR = RealIntervalField(default_prec)
CIF = ComplexIntervalField(default_prec)
def toRRR(elt, drop = True):
    if "." in elt and len(elt) > 70:
        # drop the last digit and convert it to an unkown
        if 'E' in elt:
            begin, end = elt.split("E")
        elif 'e' in elt:
            begin, end = elt.split("E")
        else:
            begin = elt
            end = "0"
        if drop:
            begin = begin[:-1] # drop the last digit
        return RRR(begin + "0e" + end, begin + "9e" + end)
    else:
        return RRR(elt)

def toCCC(r, i, drop = True):
    return CCC(toRRR(r, drop)) + CCC.gens()[0]*CCC(toRRR(i, drop))

def print_RRR(elt):
        if elt.contains_integer():
            try:
                return "%d" % ZZ(elt)
            except ValueError:
                pass
        return RRR(elt).str(style="question").replace('?', '')

def print_CCC(elt):
    elt = CCC(elt)
    return "[ %s, %s]" % tuple(map(print_RRR, [elt.real(), elt.imag()]))

def RIF_to_float(x):
    x = RRR(x)
    if x.contains_zero():
        return 0
    elif x.abs() < 1e-70:
        return 0
    else:
        fx = float(x)
        if fx == Infinity or fx == -Infinity:
            return repr(RR(x))
        else:
            return float(x)
def CBF_to_pair(x):
    a = CCC(x)
    return [RIF_to_float(a.real()), RIF_to_float(a.imag())]

def from_arb2(lower, upper, exp):
    return from_acb2(lower, upper, exp, 0, 0, 1)

def from_acb2(lower_real, upper_real, exp_real, lower_imag, upper_imag, exp_imag):
    return CCC(RRR(lower_real, upper_real)*2**exp_real, RRR(lower_imag, upper_imag)*2**exp_imag)

####################
# postgres stuff
###################


default_type = 'CMF'

def constant_lf(level, weight, degree):
    assert degree % 2 == 0
    output =  {
        'primitive' :  degree == 2,
        'conductor' : level**(degree//2),
        'load_key' : 'CMFs-workshop',
        'motivic_weight': weight - 1,
        'types': [default_type],
        'symmetry_type': '\N',
        'group' : 'GL2',
        'degree' : degree,
        'st_group' : '\N',
        'selfdual': '\N',
        'analytic_normalization': float(weight - 1)/2,
        'precision': '\N',
        'algebraic': True,
        'coeff_info': '\N',
        'credit' : '\N',
        'values': '\N', # no special values at the moment
        'gamma_factors': [[], [0]*(degree//2)],
        'coefficient_field': '\N', # the label of the Hecke field, we set as \N as start
        'dirichlet_coefficients' : '\N', # we already store a2 .. a10
        'trace_hash': '\N', #filled in later
        'euler_factors_factorization': '\N', #filled in later
        }
    for i in range(2,11):
        output['A' + str(i)] = '\N'

    return output

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
        'euler_factors', # as polys
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
        'dirichlet_coefficients', # the ap as algebraic numbers or complex
        'coefficient_field', # the label of the Hecke field
        'trace_hash',
        'euler_factors_factorization',
        ]
for i in range(2,11):
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
     u'conductor': u'numeric',
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
     u'z3': u'numeric',
     'trace_hash': 'bigint',
     'euler_factors_factorization': 'jsonb'}

schema_lf_types.pop('id')

for key in schema_lf_types.keys():
    assert key in schema_lf
for key in schema_lf:
    assert key in schema_lf_types, '%s not in schema_lf_types' % key



schema_instances = ['url', 'Lhash', 'type', 'Lhash_array']

schema_instances_types = {u'Lhash': u'text', u'id': u'bigint', u'type': u'text', u'url': u'text', u'Lhash_array': u'text[]'}
schema_instances_types.pop('id')


#######################
# End of postgres stuff
########################



def read_lfunction_file(filename):
    """
    reads an .lfunction file
    adds to it the order_of_vanishing
    and Lhash


    expects:
    root_number as acb2, see from_acb2
    order_of_vanishing
    L(1/2)^r / r! as arb2
    n = number of zeros computed
    z1 as arb2
    z2 as arb2
    z3 as arb2
    ...
    zn as arb2
    plot_delta
    number of plot_values
    plot_value1
    plot_value2
    ...
    """
    output = {}
    with open(filename, "r") as lfunction_file:
        for i, l in enumerate(lfunction_file):
            if i == 0:
                # Root number
                vals = map(int, l.split())
                if len(vals) == 1:
                    return read_lfunction_file_old(filename)
                assert len(vals) == 6
                root_number = from_acb2(*vals)
                assert root_number.abs().contains_exact(1), "%s, %s" % (filename, root_number.abs() )
                try:
                    root_number = ZZ(root_number)
                    if root_number == 1:
                        sign_arg = 0
                    elif root_number == -1:
                        sign_arg = 0.5
                    else:
                        assert root_number in [1, -1], "%s %s" % (root_number, from_acb2(*vals))
                except Exception:
                    sign_arg = float(root_number.arg()/(2*pi))
                root_number = CIF(root_number) # for conversion to text purposes
                output['root_number'] = root_number;
                output['sign_arg'] = sign_arg;
            elif i == 1:
                # Order of vanishing
                output['order_of_vanishing'] = int(l);
            elif i == 2:
                # Leading term
                # L^(r)(1/2) / r!
                vals = map(int, l.split())
                assert len(vals) == 3
                output['leading_term'] = RRR(from_arb2(*vals)).str(style="question").replace('?', '')
            elif i == 3:
                # Number of zeros
                number_of_zeros = int(l);
                output['positive_zeros'] = [];
            elif i < 4 +  number_of_zeros:
                vals = map(int, l.split())
                assert len(vals) == 3
                if vals == [0,0,0]:
                    int_zero = 0
                    double_zero = 0
                    assert 4 +  output['order_of_vanishing'] > i, "%s, %s < %s" % (filename, 5 +  output['order_of_vanishing'], i);
                else:
                    assert 4 +  output['order_of_vanishing'] <= i,  "%s, %s >= %s" % (filename, 5 +  output['order_of_vanishing'], i);
                    assert vals[1] - vals[0] <= 2, "%s %s %s" % (filename, vals, i)
                    arb_zero = from_arb2(*vals).real()
                    double_zero = float(arb_zero)
                    if 'accuracy' not in output:
                        # if vals[3] = -101
                        # then accuracy = 100
                        output['accuracy'] = -vals[2] - 1
                        two_power = 2**output['accuracy']
                    else:
                        assert -(output['accuracy'] + 1) == vals[2]
                    try:
                        int_zero = ZZ(arb_zero*two_power)
                    except ValueError:
                        print "%s %s %s" % (filename, vals, i)
                        raise
                    zero = RealNumber(int_zero.str()+".")/two_power;
                    zero_after_string = (RealNumber(zero.str(truncate=False)) * two_power).round()
                    assert double_zero == zero, "%s, %s != %s" % (filename, double_zero, zero)
                    assert zero_after_string  == int_zero, "zero_after_field = %s\nint_zero = %s" % (zero_after_string, int_zero,)
                    # will be converted to strings later on
                    # as zero.str(truncate=False)
                    # during populate_rational_rows
                    output['positive_zeros'] += [zero];
                    #Lhash = (first_zero * 2^100).round()
                    if 'Lhash' not in output:
                        output['Lhash'] = str( QQ(int_zero*2**(100 - output['accuracy'])).round() )
                        if output['accuracy'] < 100:
                            output['Lhash'] = "_" +  output['Lhash'];
            elif i == 4 +  number_of_zeros:
                output['plot_delta'] = float(l);
            elif i == 5 +  number_of_zeros:
                len_plot_values = int(l);
                output['plot_values'] = [];
            elif i >  5 + number_of_zeros:
                output['plot_values'] += [float(l)];
    assert len(output['plot_values']) == len_plot_values, "%s, %s != %s" % (filename, len(output['plot_values']), len_plot_values)
    assert len(output['positive_zeros']) ==  number_of_zeros - output['order_of_vanishing'], "%s, %s != %s" % (filename, len(output['positive_zeros']),  output['number_of_zeros'] - output['order_of_vanishing']) ;

    assert 'Lhash' in output, "%s" % filename
    for i in range(0,3):
        # were we don't want to truncate
        output['z' + str(i + 1)] = str(output['positive_zeros'][i])

    return output



def read_lfunction_file_old(filename):
    """
    reads an .lfunction file
    adds to it the order_of_vanishing
    and Lhash


    expects:
    <target accuracy> + 1
    ZZ(root_number * 2^<target accuracy>) ???
    ZZ(L(1/2) * 2^<target accuracy>)
    order_of_vanishing
    n = number of zeros computed
    z1
    z2
    z3
    ...
    zn
    plot_delta
    number of plot_values
    plot_value1
    plot_value2
    ...
    """

    output = {};
    with open(filename, "r") as lfunction_file:
        for i, l in enumerate(lfunction_file):
            if i == 0:
                accuracy = int(l) - 1;
                output['accuracy'] = accuracy;
                two_power = 2 ** output['accuracy'];
                R = ComplexIntervalField(accuracy)
            elif i == 1:
                root_number  = R(*map(ZZ, l.split(" ")))/two_power;
                if (root_number - 1).contains_zero():
                    root_number = R(1);
                    sign_arg = 0;
                elif (root_number + 1).contains_zero():
                    root_number = R(-1);
                    sign_arg = 0.5
                else:
                    assert (root_number.abs() - 1).contains_zero(), "%s, %s" % (filename, root_number.abs() )
                    sign_arg = float(root_number.arg()/(2*pi))
                    root_number = root_number #.str(style="question").replace('?', '')
                output['root_number'] = root_number;
                output['sign_arg'] = sign_arg
            elif i == 2:
                output['leading_term'] = (R(ZZ(l))/two_power).str(style="question").replace('?', '');
            elif i == 3:
                output['order_of_vanishing'] = int(l);
                if output['order_of_vanishing'] > 0:
                    output['leading_term'] = '\N'
            elif i == 4:
                number_of_zeros = int(l);
                output['positive_zeros'] = [];
            elif i < 5 +  number_of_zeros:
                double_zero, int_zero = l.split(" ");
                double_zero = float(double_zero);
                int_zero = ZZ(int_zero);
                zero = RealNumber(int_zero.str()+".")/two_power;
                zero_after_string = (RealNumber(zero.str(truncate=False)) * two_power).round()
                assert double_zero == zero, "%s, %s != %s" % (filename, double_zero, zero)
                assert zero_after_string  == int_zero, "zero_after_field = %s\nint_zero = %s" % (zero_after_string, int_zero,)
                if int_zero == 0:
                    assert 5 +  output['order_of_vanishing'] > i, "%s, %s < %s" % (filename, 5 +  output['order_of_vanishing'], i);
                else:
                    assert 5 +  output['order_of_vanishing'] <= i,  "%s, %s >= %s" % (filename, 5 +  output['order_of_vanishing'], i);

                    # they will be converted to strings later on
                    # during populate_rational_rows
                    output['positive_zeros'] += [zero];
                    #Lhash = (first_zero * 2^100).round()
                    if 'Lhash' not in output:
                        output['Lhash'] = str( QQ(int_zero*2**(100 - accuracy)).round() )
                        if accuracy < 100:
                            output['Lhash'] = "_" +  output['Lhash'];
            elif i == 5 +  number_of_zeros:
                output['plot_delta'] = float(l);
            elif i == 6 +  number_of_zeros:
                len_plot_values = int(l);
                output['plot_values'] = [];
            elif i >  6 + number_of_zeros:
                output['plot_values'] += [float(l)];

    assert len(output['plot_values']) == len_plot_values, "%s, %s != %s" % (filename, len(output['plot_values']), len_plot_values)
    assert len(output['positive_zeros']) ==  number_of_zeros - output['order_of_vanishing'], "%s, %s != %s" % (filename, len(output['positive_zeros']),  output['number_of_zeros'] - output['order_of_vanishing']) ;


    assert 'Lhash' in output, "%s" % filename
    for i in range(0,3):
        output['z' + str(i + 1)] = str(output['positive_zeros'][i])

    return output

def extend_multiplicatively(Z):
    for pp in prime_powers(len(Z)-1):
        for k in range(1, (len(Z) - 1)//pp + 1):
            if gcd(k, pp) == 1:
                Z[pp*k] = Z[pp]*Z[k]

def dirichlet(R, euler_factors):
    PS = PowerSeriesRing(R)
    pef = zip(primes_first_n(len(euler_factors)), euler_factors)
    an_list_bound = next_prime(pef[-1][0])
    res = [1]*an_list_bound
    for p, ef in pef:
        k = RR(an_list_bound).log(p).floor()+1
        foo = (1/PS(ef)).padded_list(k)
        for i in range(1, k):
            res[p**i] = foo[i]
    extend_multiplicatively(res)
    return res


#def read_euler_factors(filename, prec = default_prec, number_of_euler_factors = 30, an_list_bound = 11):
#    CCC = ComplexBallField(prec)
#    PS = PowerSeriesRing(CCC)
#    def read_euler_factor_CC_line(line):
#        #expects p, [[1,0], [a1.re, a1.imag],...] per line
#        line = line.replace(" ", "")
#        p, euler = line.split(',',1)
#        p = int(p)
#        euler_factor = [CCC(*elt.split(',')) for elt in line.split(',',1)[1].replace(" ", "").rstrip(']]').lstrip('[[').split('],[')]
#        # try to round integers
#        euler_factor = [elt.round() if elt.contains_integer() else elt for elt in euler_factor]
#        assert euler_factor[0] == 1
#        return p, euler_factor
#
#    euler_factors = []
#    bad_euler_factors = []
#
#
#
#    dirichlet = [1]*an_list_bound
#    lpdata_file = open(filename, "r");
#    for l in lpdata_file:
#        p, lp = read_euler_factor_CC_line(l);
#        if len(lp) <= 2:
#            bad_euler_factors += [[p, lp]]
#        if len(euler_factors) < number_of_euler_factors:
#            euler_factors += [lp]
#
#        if p < an_list_bound:
#            k = RR(an_list_bound).log(p).floor()+1
#            foo = (1/PS(lp)).padded_list(k)
#            for i in range(1, k):
#                dirichlet[p**i] = foo[i]
#        if len(euler_factors) == number_of_euler_factors:
#            break
#
#    assert number_of_euler_factors == len(euler_factors)
#    extend_multiplicatively(dirichlet)
#
#    return euler_factors, bad_euler_factors, dirichlet



####
def prod_plot_values(factor_plot_deltas, factor_values):
    assert len(factor_plot_deltas) == len(factor_values)
    halfdegree = len(factor_values)
    if halfdegree == 1:
        return factor_plot_deltas[0], factor_values[0]
    factor_plot_values = [ [ ( j * factor_plot_deltas[k],  z) for j, z in enumerate(values) ] for k, values in enumerate(factor_values)]
    interpolations = [spline(elt) for elt in factor_plot_values]
    max_delta = max(factor_plot_deltas)
    new_delta = max_delta/halfdegree
    plot_range = min( [elt[-1][0] for elt in factor_plot_values] )
    values = [prod([elt(i) for elt in interpolations]) for i in srange(0, plot_range, new_delta)]
    return new_delta, values

def from_power_sums(ps):
    assert ps[0] is None
    es = [None] * len(ps)
    es[0] = 1
    if len(ps) > 1:
        es[1] = ps[1]
        for k in range(2, len(ps)):
            es[k] = sum( (-1)**(i -1) * es[k-i] * ps[i] for i in range(1, k + 1))/k
        es = [(-1)**i * elt for i, elt in enumerate(es)]
    return es

# sqrt hack for ComplexBallField
def sqrt_hack(foo):
    if not foo.real().contains_zero() and foo.real().mid() < 0:
        return foo.parent().gens()[0] * (-foo).sqrt()
    else:
        return foo.sqrt()


def reciprocal_roots(coeff):
    if len(coeff) == 3:
        a, b ,c = coeff;
        sqrtdisc = sqrt_hack(b**2 - 4*a*c)
        alpha1 = (-b + sqrtdisc)/(2*a)
        alpha2 = (-b - sqrtdisc)/(2*a)
        return [alpha1, alpha2]
    elif len(coeff) == 2:
        a, b = coeff
        return [-b/a]

def rational_euler_factors(euler_factors_cc, level, weight, an_list_bound = 11):
    dirichlet = [1]*an_list_bound
    dirichlet[0] = 0
    euler_factors = []
    bad_lfactors = []
    halfdegree = len(euler_factors_cc)
    PS = PowerSeriesRing(ZZ, "X")
    CCCx = PolynomialRing(CCC, "x")
    todo = list(enumerate(primes_first_n(30)))
    for p in sorted(ZZ(level).prime_divisors()):
        p_index = prime_pi(p) - 1
        if p_index >= 30:
            todo.append((p_index, p))
    for p_index, p in todo:
        if p_index >= len(euler_factors_cc[0]):
            assert level % p == 0, "%s, %s, %s"  % (level, weight, len(euler_factors_cc))
            bad_lfactors.append([int(p), [int(1)] + [None]*halfdegree])
            continue

        #try to guess the rest by multiplying them
        roots = []
        for lf in euler_factors_cc:
            roots += reciprocal_roots(lf[p_index])
        root_powers = [None] * (halfdegree + 1)
        for j in range(1,halfdegree + 1):
            try:
                root_powers[j] = RRR(sum( map(lambda z: (z**j).real(), roots) )).unique_integer()
            except ValueError:
                root_powers = root_powers[:j]
                break
        partial_efzz = from_power_sums(root_powers)
        efzz = map(int, partial_efzz) + [None]*(halfdegree +1 - len(partial_efzz))
        # to check that from_power_sums is correct
        ef = prod([CCCx(lf[p_index]) for lf in euler_factors_cc])
        for j, elt in enumerate(ef.list()[:len(partial_efzz)]):
            try:
                efj = int(RRR(elt.real()).unique_integer())
            except ValueError:
                #print j
                #print RRR(elt.real())
                #print p
                #print "[%s]" % (", ".join(["[%s]" % (", ".join(map(print_CCC, lf[p_index]))) for ef in euler_factors_cc]))
                #assert False
                break;
            assert efj == efzz[j], "%s, %s, %s, %s != %s"  % (level, weight, len(euler_factors_cc), efj, efzz[j])


        if (level % p) != 0:
            sign = RRR(ef.list()[-1].real()/p**((halfdegree)*(weight - 1))).unique_integer()
            assert sign in [1,-1], "%s\n%s" % (RRR(prod( lf[p_index][2] for lf in euler_factors_cc).real()).unique_integer(),p**((halfdegree)*(weight - 1)))
            efzz2 = [None] * halfdegree
            for i, elt in enumerate(reversed(efzz[:-1])):
                if elt is None:
                    efzz2[i] = None
                else:
                    efzz2[i] = int(sign*p**((i+1)*(weight - 1)) * elt)
            efzz += efzz2
            euler_factors.append(efzz)
        else:
            if None not in efzz:
                k = len(efzz)
                while efzz[k - 1] == 0 and k >= 1:
                    k -= 1
                efzz = efzz[:k]
            bad_lfactors.append([int(p), efzz])
            if p_index < 30:
                euler_factors.append(efzz)
        if p < an_list_bound:
            k = RR(an_list_bound).log(p).floor()+1
            foo = (1/PS(efzz)).padded_list(k)
            for i in range(1, k):
                dirichlet[p**i] = foo[i]

    extend_multiplicatively(dirichlet)

    assert len(euler_factors) == 30, "%s, %s, %s, %s != 30"  % (level, weight, len(euler_factors_cc), len(euler_factors))

    return euler_factors, bad_lfactors, dirichlet


def populate_rational_rows(orbits, euler_factors_cc, rows, instances):
    rational_rows = {}
    order_of_vanishing = schema_lf_dict['order_of_vanishing']
    accuracy = schema_lf_dict['accuracy']
    positive_zeros = schema_lf_dict['positive_zeros']
    sign_arg = schema_lf_dict['sign_arg']
    Lhash = schema_lf_dict['Lhash']
    plot_delta = schema_lf_dict['plot_delta']
    plot_values = schema_lf_dict['plot_values']
    central_character = schema_lf_dict['central_character']
    positive_zeros = schema_lf_dict['positive_zeros']
    leading_term = schema_lf_dict['leading_term']
    root_number = schema_lf_dict['root_number']
    k = 0
    for mf_orbit_label, labels in orbits.iteritems():
        try:
            level, weight, char_orbit, hecke_orbit = mf_orbit_label.split(".")
            level, weight = map(int, [level, weight])
            # read and convert zeros to str
            # is important to do this before converting them
            zeros_as_real = []
            root_numbers = []
            for elt in labels:
                zeros_factor = rows[elt][positive_zeros]
                zeros_as_real.extend( zeros_factor )
                # and now convert them to strings
                zeros_factor = [ z.str(truncate=False) for z in zeros_factor]
                rows[elt][positive_zeros] = str(zeros_factor).replace("'","\"")
                # same for root numbers
                root_numbers.append(rows[elt][root_number])
                rows[elt][root_number] = rows[elt][root_number].str(style="question").replace('?', '')

            # for now skip degree > 80
            # no more, now the limit is 40
            if len(labels) > 20: # the real limit is 87
                continue
            degree = 2*len(labels)
            row = constant_lf(level, weight, degree)
            row['origin'] = "ModularForm/GL2/Q/holomorphic/%d/%d/%s/%s" % (level, weight, char_orbit, hecke_orbit)
            row['self_dual'] = True
            row['conjugate'] = '\N'
            row['order_of_vanishing'] = sum([rows[elt][order_of_vanishing] for elt in labels])
            row['accuracy'] = min([rows[elt][accuracy] for elt in labels])


            zeros_as_real.sort()
            zeros_as_str = [ z.str(truncate=False) for z in zeros_as_real]
            row['positive_zeros'] = str(zeros_as_str).replace("'","\"")
            row['Lhash'] = ",".join(map(str, sorted([int(rows[elt][Lhash]) for elt in labels])))
            for i in range(0,3):
                row['z' + str(i + 1)] = str(zeros_as_real[i])


            # character
            if degree == 2:
                row['central_character'] = rows[labels[0]][central_character]
            else:
                G = DirichletGroup_conrey(level)
                chiprod = prod([G[ int(rows[elt][central_character].split(".")[-1]) ] for elt in labels])
                chiprod_index = chiprod.number()
                row['central_character'] = "%s.%s" % (level, chiprod_index)

            row['sign_arg'] = sum([rows[elt][sign_arg] for elt in labels])
            while row['sign_arg'] > 0.5:
                row['sign_arg'] -= 1
            while row['sign_arg'] <= -0.5:
                row['sign_arg'] += 1

            deltas = [rows[elt][plot_delta] for elt in labels]
            values = [rows[elt][plot_values] for elt in labels]
            row['plot_delta'], row['plot_values'] = prod_plot_values(deltas, values)
            row['leading_term'] = (prod(toRRR(rows[elt][leading_term], drop=False) for elt in labels)).str(style="question").replace('?', '')
            try:
                row['root_number'] = str(RRR(prod(root_numbers).real()).unique_integer())
                if row['root_number'] == str(1):
                    row['sign_arg'] = 0
                elif row['root_number'] == str(-1):
                    row['sign_arg'] = 0.5
                else:
                    assert row['root_number'] in map(str, [1, -1]), "%s" % row['root_number']
            except ValueError:
                # couldn't pin down the unique integer through root_numbers
                row['root_number'] = str(RRR(CDF(exp(2*pi*I*row['sign_arg'])).real()).unique_integer())
            row['coefficient_field'] = '1.1.1.1'



            euler_factors = [euler_factors_cc[elt] for elt in labels]
            row['euler_factors'], row['bad_lfactors'], dirichlet = rational_euler_factors(euler_factors, level, weight)

            # fill in ai
            for i, ai in enumerate(dirichlet):
                if i > 1:
                    row['a' + str(i)] = int(dirichlet[i])
                    #print 'a' + str(i), dirichlet[i]


            for key in schema_lf:
                assert key in row, "%s not in row = %s" % (key, row.keys())
            for key in row.keys():
                assert key in schema_lf, "%s unexpected"  % key
            assert len(row) == len(schema_lf), "%s != %s" % (len(row) , len(schema_lf))

            #rewrite row as a list
            rational_rows[mf_orbit_label] = [row[key] for key in schema_lf]
            instances[mf_orbit_label] = (row['origin'], row['Lhash'], 'CMF', json.dumps(row['Lhash'].split(',')).replace('[','{').replace(']','}'))

            # if dim == 1, drop row
            if len(labels) == 1:
                rows.pop(labels[0])
                instances.pop(labels[0])
        except Exception:
            print mf_orbit_label, labels
            raise


        k += 1
        if len(orbits) > 10:
            if (k % (len(orbits)//10)) == 0:
                print "populate_rational_rows %.2f%% done" % (k*100./len(orbits))

    print "populate_rational_rows done"
    return rational_rows

def self_dual(char, aps):
    if char.is_trivial():
        return True
    if (char*char).is_trivial():
        for _, z in aps:
            if not z.imag().contains_zero():
                return False
        else:
            return True
    else:
        return False

def write_header(lfunctions_filename, instances_filename, overwrite = True):

    str_parsing_lf = '\t'.join(['%s'] * len(schema_lf)) + '\n'
    str_parsing_instances = '\t'.join(['%s'] * len(schema_instances)) + '\n'
    if not os.path.exists(lfunctions_filename) or overwrite:
        with open(lfunctions_filename,"w") as F:
            F.write(str_parsing_lf % tuple(schema_lf))
            F.write(str_parsing_lf % tuple([schema_lf_types[key] for key in schema_lf]))
            F.write("\n")

    if not os.path.exists(instances_filename) or overwrite:
        with open(instances_filename, "w") as F:
            F.write(str_parsing_instances % tuple(schema_instances))
            F.write(str_parsing_instances % tuple([schema_instances_types[key] for key in schema_instances]))
            F.write("\n")

def export_lfunctions(rows, rational_rows, instances, lfunctions_filename, instances_filename):
    print "Writing to %s and %s" % (lfunctions_filename, instances_filename)
    write_header(lfunctions_filename, instances_filename)
    def json_hack(elt):
        if isinstance(elt, str):
            return elt
        else:
            return json.dumps(elt)
    assert len(rows) + len(rational_rows) == len(instances)
    with open(lfunctions_filename, 'a') as LF:
        for key, row in rows.iteritems():
            LF.write("\t".join(map(json_hack,row)) + "\n")

        for key, row in rational_rows.iteritems():
            LF.write("\t".join(map(json_hack,row)) + "\n")

    with open(instances_filename, 'a') as IF:
        for key, row in instances.iteritems():
            IF.write("\t".join(map(json_hack,row)) + "\n")


def line_count(filename):
    i = 0
    with open(filename, 'r') as F:
        for _ in F:
            i += 1
    return i

def check_all_files(filename, linecount, chunk = 100):
    k = 0
    base_dir = os.path.dirname(os.path.abspath(filename))
    lfun_dir = os.path.join(base_dir, 'lfun')
    inputs_dir = os.path.join(base_dir, 'inputs')
    inputs = {}
    with open(filename, 'r') as F:
        for line in F:
            linesplit = line[:-1].split(':')
            hoc, label, conrey_label_tmp, embedding_index_tmp, embedding_m, ap_txt = linesplit
            lpdatafilename = os.path.join(lfun_dir, label + ".lpdata")
            lfunfilename = os.path.join(lfun_dir, label + ".lpdata.lfunction")

            if not os.path.exists(lpdatafilename):
                print "%s\tMissing lpdata file: %s" % (label, lpdatafilename)

                print "Use generate_lpdata_and_inputs.py to generate those files"
                sys.exit(1)
            if not os.path.exists(lfunfilename):
                print "%s\tMissing lfunction file: for %s" % (label, lfunfilename)
                # reading the line
                level, weight, char_orbit, hecke_orbit, conrey_label, embedding_index = label.split(".")
                level, weight, conrey_label, embedding_index = map(int, [level, weight, conrey_label, embedding_index])
                ap_list = [ toCCC(*elt.split(',')) for elt in ap_txt[2:-2].split('],[')]
                ap_list = zip(primes_first_n(len(ap_list)),ap_list)
                G = DirichletGroup_conrey(level, CCC)
                char = DirichletCharacter_conrey(G, conrey_label)
                if weight not in inputs:
                    inputs[weight] = []
                inputs[weight].append("%d %d %d %s %s" % (weight, self_dual(char, ap_list) , level, label, lpdatafilename))
            k += 1
            if linecount > 10:
                if (k % (linecount//10)) == 0:
                    print "check_all_files %.2f%% done" % (k*100./linecount)
    if len(inputs) > 0:
        real_filename = os.path.abspath(filename).split('/')[-1]
        parallel_inputs = os.path.join(base_dir, real_filename + '.tsv.missing')
        with open(parallel_inputs, 'w') as I:
            for weight, lines in inputs.iteritems():
                if chunk is None:
                    chunked_lines = [lines]
                else:
                    chunked_lines = [ lines[i:i+chunk] for i in range(0, len(lines), chunk)]
                assert sum(map(len, chunked_lines)) == len(lines), "%d != %d" % (sum(map(len, chunked_lines)), len(lines))
                for i, line_block in enumerate(chunked_lines):
                    inputsfilename = os.path.join(inputs_dir, real_filename + '_wt%d_%d.missing.input' % (weight, i))
                    with open(inputsfilename , 'w') as W:
                        W.write('\n'.join(line_block) + '\n')
                        #print "wrote %d lines to %s" % (len(line_block), inputsfilename)
                    I.write("%d\t%s\n" % (weight, inputsfilename))
        print "There were some missing lfunction files!"
        print "please set LFUNCTIONS and run:"
        print r"""parallel -a %s  --colsep '\t' --progress ${LFUNCTIONS}/euler_factors 11 200  ${LFUNCTIONS}/gamma_files/mf.{1} {2} 100""" % (parallel_inputs,)
        sys.exit(1)


    print "check_all_files done"
    return None

def read_all(filename):
    # label -> [p, Lp]
    euler_factors_cc = {}
    # label -> labels
    orbits = {}
    # label -> postgres row as list
    rows = {}
    instances = {}


    base_dir = os.path.dirname(os.path.abspath(filename))
    lfun_dir = os.path.join(base_dir, 'lfun')
    linecount = line_count(filename)
    check_all_files(filename, linecount)

    k = 0
    with open(filename, 'r') as F:
        for line in F:
            linesplit = line[:-1].split(':')
            hoc, label, conrey_label_tmp, embedding_index_tmp, embedding_m, ap_txt = linesplit
            level, weight, char_orbit, hecke_orbit, conrey_label, embedding_index = label.split(".")
            assert conrey_label_tmp == conrey_label
            assert embedding_index_tmp == embedding_index
            mf_orbit_label = ".".join([level, weight, char_orbit, hecke_orbit])
            if mf_orbit_label not in orbits:
                orbits[mf_orbit_label] = []
            orbits[mf_orbit_label].append(label)

            ap_list = [ toCCC(*elt.split(',')) for elt in ap_txt[2:-2].split('],[')]
            ap_list = zip(primes_first_n(len(ap_list)),ap_list)

            lpfilename = os.path.join(lfun_dir, label + ".lpdata")
            lffilename = os.path.join(lfun_dir, label + ".lpdata.lfunction")

            if not all(map(os.path.exists, [lpfilename, lffilename])):
                continue

            level, weight, conrey_label, embedding_index = map(int, [level, weight, conrey_label, embedding_index])

            G = DirichletGroup_conrey(level, CCC)
            char = DirichletCharacter_conrey(G, conrey_label)


            # the basis
            row = constant_lf(level, weight, 2)
            row['origin'] = "ModularForm/GL2/Q/holomorphic/%d/%d/%s/%s/%d/%d" % (level, weight, char_orbit, hecke_orbit, conrey_label, embedding_index)
            row['self_dual'] = self_dual(char, ap_list)
            row['central_character'] = "%s.%s" % (level, conrey_label)
            # sets accuracy, root_number, sign_arg, leading_term, order_of_vanishing, positive_zeros, plot_delta, plot_values
            for key, val in read_lfunction_file(lffilename).iteritems():
                row[key] = val

            if row['self_dual']:
                row['conjugate'] = '\N'
            else:
                lfconjfilename=  os.path.join(lfun_dir, label + ".lpdata.conj.lfunction")
                assert os.path.exists(lfconjfilename)
                row['conjugate'] = read_lfunction_file(lfconjfilename)['Lhash']


            def euler_factor(p, ap):
                if p.divides(level):
                    return [1, -ap]
                charval = CCC(2*char.logvalue(p)).exppii()
                if charval.contains_exact(ZZ(1)):
                    charval = 1
                elif charval.contains_exact(ZZ(-1)):
                    charval = -1
                return [1, -ap, (p**(weight-1))*charval]
            cut = 30 if level == 1 else max(30, prime_pi(max(prime_divisors(level))))
            euler_factors = [ euler_factor(*elt) for elt in ap_list[:cut] ]
            bad_euler_factors = [ [elt[0], euler_factor(*elt)] for elt in ap_list if elt[0].divides(level)]

            euler_factors_cc[label] = euler_factors
            row['euler_factors'] = map( lambda x : map(CBF_to_pair, x), euler_factors)
            row['bad_lfactors'] =  map( lambda x: [int(x[0]), map(CBF_to_pair, x[1])], bad_euler_factors)
            row['coefficient_field'] = 'CDF'
            for i, ai in enumerate(dirichlet(CCC, euler_factors[:11])[2:12]):
                if i + 2 <= 10:
                    row['a' + str(i+2)] = CBF_to_pair(ai)


            for key in schema_lf:
                assert key in row, "%s not in row = %s" % (key, row)
            assert len(row) == len(schema_lf), "%s != %s" % (len(row) , len(schema_lf))
            rows[label] = [row[key] for key in schema_lf]
            instances[label] = (row['origin'], row['Lhash'], 'CMF')
            k += 1
            if linecount > 10:
                if (k % (linecount//10)) == 0:
                    print "read_all %.2f%% done" % (k*100./linecount)
    print "read_all Done"

    rational_rows = populate_rational_rows(orbits, euler_factors_cc, rows, instances)
    
    positive_zeros = schema_lf_dict['positive_zeros']
    for elt, val in rows.iteritems():
        assert isinstance(val[positive_zeros], str), "%s, %s, %s" % (elt, type(val[positive_zeros]), val[positive_zeros])
    lfun_filename = filename + ".lfunctions"
    instances_filename = filename + ".instances"
    export_lfunctions(rows, rational_rows, instances, lfun_filename, instances_filename)
    return 0





read_all(sys.argv[1])

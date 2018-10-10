from dirichlet_conrey import DirichletGroup_conrey
from sage.all import ZZ, power_mod, prod
def index_above(n, k ,c):
    if c == 1:
        return 1
    if c == n - 1:
        if n % 2 == 1 or n % 4 == 0:
        return n**k - 1
    h = DirichletGroup_conrey(n)[c].primitive_character()
    assert (h*h).is_trivial()
    G = DirichletGroup_conrey(n**k)
    tor2 = []
    for g in G.gens():
        mo =  G[g].multiplicative_order()
        if mo % 2 == 0:
            #print g, mo
            tor2.append(power_mod(g, mo//2, G.modulus()))

    # try to see if is just a generator
    for t in tor2:
        if h == G[t].primitive_character():
            return t


    for k in range(2**len(tor2)):
        if ZZ(k).popcount() == 1:
            continue
        chi = prod([ G[t] for t, l in zip(tor2, ZZ(k).digits(base = 2, padto = len(tor2))) if l != 0])
        if chi != 1 and chi.primitive_character() == h:
            return chi.number()
def wrapper_index_above(n, k, c):
    try:
        if n**k >= 2**32:
            raise AttributeError
        C = index_above(n, k, c)
        N = n**k
        if C is None:
            raise AttributeError
    except (NotImplementedError, AttributeError):
        C = c
        N = n
    return '%s.%s' % (N, C)

import sys
n, k, c = map(int, sys.argv[1:4])
print wrapper_index_above(n, k, c)


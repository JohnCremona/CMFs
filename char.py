# Sage functions for computing the ordered list of Galois orbits of Dirichlet characters

# The main function DirichletCharacterGaloisReps(N) returns a list of
# "Dirichlet-Conrey" characters, while
# GP_DirichletCharacterGaloisReps(N) returns the characters in a form
# usable in gp. We use DC characters since its the easiest way to
# convert into gp characters

from dirichlet_conrey import DirichletGroup_conrey as DG, DirichletCharacter_conrey as DC
from sage.all import pari, ZZ, gcd, euler_phi,Mod

def character_traces(chi):
    return [chi(j).trace() for j in range(chi.modulus())]

DCGR_cache={}

def DirichletCharacterGaloisReps(N):
    global DCGR_cache
    if not N in DCGR_cache:
        Chars = [ch[0] for ch in DG(N).galois_orbits()]
        vv = [[[DC.multiplicative_order(chi)]+character_traces(DC.sage_character(chi)),i] for i,chi in enumerate(Chars)]
        vv.sort()
        DCGR_cache[N] = [Chars[v[1]] for v in vv]
    return DCGR_cache[N]

def NChars(N):
    return ZZ(sum([1/euler_phi(Mod(i,N).multiplicative_order()) for i in range(N) if gcd(i,N)==1]))

# To obtain the index number of a character chi use DC.number(chi)

def OrderedConreyLabels(N):
    return [DC.number(chi) for chi in DirichletCharacterGaloisReps(N)]

#NB if using the preceding function to compare with other
# implementations, note that we picked an arbitrary representative for
# each Galois orbit, so the lists might not natch exactly, but if any
# number appears in both lists, it must be in the same place in each!

# If the following is to be called repeatedly with the same modulus it
# is better to precompute G and pass it, so save recomputation:

def DC_char_to_gp_char(chi, G=None):
    if G==None:
        G = pari(chi.modulus()).znstar(1)
    return G.znconreylog(DC.number(chi))

def GP_DirichletCharacterGaloisReps(N):
    G = pari(N).znstar(1)
    return [G.znconreylog(DC.number(chi)) for chi in DirichletCharacterGaloisReps(N)]

char_table_dict = None

def char_orbit_index_to_DC_number(N,o):
    """Returns the index in the Dirichlet-Conrey numbering of one character in orbit number o"""
    global char_table_dict
    if not char_table_dict:
        char_table_dict = {}
        try:
            chartab = open("chartab.txt")
            for L in chartab.readlines():
                NN, oo, nn = [int(x) for x in L.split()]
                if not NN in char_table_dict:
                    char_table_dict[NN] = {}
                char_table_dict[NN][oo] = nn
            chartab.close()
        except IOError:
            Chars = DirichletCharacterGaloisReps(N)
            return DC.number(Chars[o-1])
    return char_table_dict[N][o]

# Sage functions for computing the ordered list of Galois orbits of Dirichlet characters

# The main function DirichletCharacterGaloisReps(N) returns a list of
# "Dirichlet-Conrey" characters, while
# GP_DirichletCharacterGaloisReps(N) returns the characters in a form
# usable in gp. We use DC characters since its the easiest way to
# convert into gp characters

from dirichlet_conrey import DirichletGroup_conrey as DG, DirichletCharacter_conrey as DC
from sage.interfaces.gp import gp

def character_traces(chi):
    return [chi(j).trace() for j in range(chi.modulus())]


def DirichletCharacterGaloisReps(N):
    Chars = [ch[0] for ch in DG(N).galois_orbits()]
    vv = [[[DC.multiplicative_order(chi)]+character_traces(DC.sage_character(chi)),i] for i,chi in enumerate(Chars)]
    vv.sort()
    return [Chars[v[1]] for v in vv]

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
        G = gp.znstar(chi.modulus(),1)
    return gp.znconreylog(G,DC.number(chi))

def GP_DirichletCharacterGaloisReps(N):
    G = gp.znstar(N,1)
    return [gp.znconreylog(G,DC.number(chi)) for chi in DirichletCharacterGaloisReps(N)]

import os
import sys
from sage.all import ZZ
from mf_pari import OneSpace

N,k,o,dmax,nan = [ZZ(c) for c in sys.argv[1].split()]

OneSpace(N,k,o,dmax,nan,filename="wt1data/data.txt")

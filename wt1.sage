import os
import sys
from char import NChars

nargs = len(sys.argv)
assert nargs >= 3

try:
    N1 = int(sys.argv[1])
except ValueError:
    print("{} is not valid argument (arg 1)".format(sys.argv[1]))
    raise RuntimeError
try:
    N2 = int(sys.argv[2])
except ValueError:
    print("{} is not valid argument (arg 2)".format(sys.argv[2]))
    raise RuntimeError

dmax = 0
if nargs >= 4:
    try:
        dmax = int(sys.argv[3])
    except ValueError:
        print("{} is not valid argument (arg 3)".format(sys.argv[3]))
        raise RuntimeError


nan = 1000
if nargs >= 5:
    try:
        nan = int(sys.argv[4])
    except ValueError:
        print("{} is not valid argument (arg 4)".format(sys.argv[4]))
        raise RuntimeError

print("read args N1={}, N2={}, dmax={}, nan={}".format(N1,N2,dmax,nan))

outfile = "wt1input.{}-{}".format(N1,N2)
out = open(outfile, mode='w')
nspaces=0
for N in [N1..N2]:
    nch = NChars(N)
    nspaces += nch
    for o in range(nch):
        out.write("{} {} {} {} {}\n".format(N,1,o+1,dmax,nan))
out.close()
print("finished writing {} lines to {}".format(nspaces,outfile))

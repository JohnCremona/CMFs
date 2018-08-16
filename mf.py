# function to read a file output by the gp or magma scripts, return
# two dictionaries both with keys (N,k,nchar), one with valies
# dimension-list, the other with times.

def read_dims(fname):
    dims_dict = {}
    times_dict = {}
    max_time = tot_time = tot_time0 = 0.0
    max_space = None
    nspaces = 0
    nspaces0 = 0 # exclude trvial spaces
    for L in open(fname).readlines():
        N,k,chi,t,dims = L.split(":")
        N=int(N)
        k=int(k)
        chi=int(chi)
        t=float(t)
        # the -2 below is because the dims string ends "]\n"
        dims = [] if  dims=="[]\n" else [int(d) for d in dims[1:-2].split(",")]
        key = (N,k,chi)
        dims_dict[key] = dims
        times_dict[key] = t
        if t>max_time:
            max_time = t
            max_space = key
        tot_time += t
        nspaces += 1
        if dims:
            nspaces0 += 1
            tot_time0 += t
    print("Read {} spaces of which {} are nontrivial.  Total cpu time = {}s".format(nspaces, nspaces0, tot_time))
    print("Max time = {} for space {}".format(max_time, max_space))
    print("Average time (all spaces)      = {}".format(tot_time/nspaces))
    print("Average time (nonzero spaces)  = {}".format(tot_time0/nspaces0))
    return dims_dict, times_dict

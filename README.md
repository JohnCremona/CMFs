CMFs
===

code and data for computing Classical Modular Forms in Pari/gp, Magma,
Sage

Code
-------

karim.gp: Karim Belabas's original function
* mf.gp: defines the DecomposeSpaces() function in gp for dimension split, traces, polnomials
* mf.m: defines the DecomposeSpaces() and ComputeCoefficientFields() funtions in Magma
* mf.py: Python (Sage) scripts for reading and comparing output from DecomposeSpaces()
* polredabs.spec defines Magma interface to polredabs and polredbest
* conrey.m: functions for converting between Galois orbits of Dirichlet characters and Conrey labels of Dirichlet characters

Data
-------

Format of mfdecomp_xxx_m.txt and mfdecomp_xxx_gp.txt files is N:k:i:t:[n1,n2,...] where N is the level, k is the weight, i is the index of the Dicihlet character orbit (sorted in reverse lex order of trace value vectors), t is cpu-time, and [n1,n2,...] is a sorted list of Q-dimensions of the minimal Galois stable subspaces of S_k^new(N,chi).

Format of mffield_xxx_m.txt is N:k:i:[n1,n2,...]:[f1,f2,...] where N,k,n1,n2,... are as in mfdecomp_xxx.m.txt and f1,f2,... are lists of integer coefficients of polredbest polynomials defining the coefficient fields (constant coefficient first) for the orbits of dimension at most 20 (so list of f's may be shorter than the list of n's).  Spaces for which the list of field polys would be empty (because the space contains no orbits of positive dimension at most 20) are ommitted.

* mfdecomp_100_10.m.txt: Magma output levels 1-100, weights 2-10 (this data is incorrect due to bug/inconsitency in magma!)
* mfdecomp_100_10.gp.txt: gp output levels 1-100, weights 2-10

* mfdecomp_500.m.txt: Magma output for Nk <= 500 (corrects inconsistency in mfdecomp_100_10 files, timings for N=1,2 are bogus)
* mfdecomp_500.gp.txt: gp output for Nk <= 500
* mfdecomp_500.txt : Galois orbit decomposition data for Nk <= 500 (as independently computed by gp and Magma)
* mffield_500.m.txt : Coefficient field data for Nk <= 500 for fields of degree d <= 20 computed in Magma

* mfdecomp_1000.gp.txt gp output for Nk <= 1000
* mfdecomp_1000.txt : Galois orbit decomposition data for Nk <= 1000 (as computed by gp, to be confirmed by Magma)

* mfdecomp_full_100.txt : Galois decomposition data for NK <= 100 computed by Magma with the following format N:k:i:t:[n1,n2,...]:[t1,t2,...]:[f1,f2,...]:[h1,h2,...], where N,k,i,t are as above, [t1,t2,...] is a list of vectors of absolute traces of Hecke eigenvalues a_n for 1<=n<=100 sorted lexicographically (this will match the order of n1,n2,.. because the trace of 1 gives the degree of the coefficient field), [f1,f2,...] is a list of polredbest-stable polynomials defining the coefficient fields for those orbits of dimension <= 20, and [h1,h2,...] is a list of pairs <p,h_p(x)> where p is a prime not dividing N and h_p(x) is the minimal polynomial of T_p (over a cyclotomic field).  The [h1,h2,...] vector only addresses spaces of dimension up to 20, and each list includes p's sufficient to uniquely distinguish each Galois orbit.  All of the vectors that occur are sorted consistently (but note that the last two match prefixes of the first two).

* mfdecomp_full_100.gp.txt : As above but output from gp, excluding the [h1,...]

* data/N1-1000k1 : dimension split for weight 1 forms, all levels to 1000.
* data/N*k* : dimension splits for various weight/level ranges including all with N*k<=1000
* data/all.txt : concatenation of previous
* data/mffield.txt : polynomials for spaces of dimension<=20, N*k<=1000


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
* polredabs.m defines Magma interface to polredabs and polredbest (use Attach("polredabs.m"))
* conrey.m: functions for converting between Galois orbits of Dirichlet characters and Conrey labels of Dirichlet characters

Data
-------

Format of mfdata_xxx.m.txt is N:k:i:t:D:T:A:F:C:E:cm:it
where:

 1) N = level
 2) k = weight
 3) i = character orbit
 4) t = time
 5) D = dims [d1,d2,...] of Galois stable subspaces
 6) T = traces [[trace(a_1),...trace(a_n)],...] one list of traces for each subspace listed in D
 7) A = Atkin-Lehner signs (empty list if character is not trivial (0=1)) [[<p,sign> for p in Divisors(N)],...], one list of Atkin-Lehner signs for each subspace listed in D
 8) F = Hecke field polys [[f0,f1,...,1],...] list of coeffs (constant coeff first), one list for each subspace listed in D of dimension up to degree-bound (currently 20)
 9) C = Hecke cutters [[<p,charpoly>,...],...] list of minimal lists of charpolys of T_p sufficient to distinguish subspaces listed in D up to degree-bound (???)
10) E = Hecke Eigenvalue data [<f,b,n,m,e>,...] list of tuples <f,b,n,c,e> of Hecke eigenvalue data for each subspace listed in D of dimension up to eigenvalue-degree-bound (currently 6) where:
      1) f is a polredbestified field poly (should be the same as corresponding poly in F),
      2) b defines a basis for the Hecke ring in terms of power basis for f (list of lists of rationals),
      3) n is an integer that divides the index of the order spanned by b in the maximal order
      4) m is a boolean (0 or 1) indicating whether n is known to be maximal
      5) e is a list of eigenvalues specified in terms of the basis b (list of d integers for each a_n, where d=deg(f))
11) cm = list of cm discriminants one for each subspace listed in D, 0 indicates no CM (all proven)
12) it = list of lists of char orbits of inner twists (empty list means no inner twists) -- NOT RIGOROUS

Format of mfdecomp_xxx_m.txt and mfdecomp_xxx_gp.txt files is N:k:i:t:D where N is the level, k is the weight, i is the index of the Dicihlet character orbit (sorted in reverse lex order of trace value vectors), t is cpu-time, and D=[n1,n2,...] is a sorted list of Q-dimensions of the minimal Galois stable subspaces of S_k^new(N,chi).

Format of mffield_xxx_m.txt is N:k:i:[n1,n2,...]:[f1,f2,...] where N,k,n1,n2,... are as in mfdecomp_xxx.m.txt and f1,f2,... are lists of integer coefficients of polredbest polynomials defining the coefficient fields (constant coefficient first) for the orbits of dimension at most 20 (so list of f's may be shorter than the list of n's).  Spaces for which the list of field polys would be empty (because the space contains no orbits of positive dimension at most 20) are ommitted.

* mfdata_100.m.txt : Magma modular forms data for Nk^2 <= 100
* mfdata_1000.m.txt : Magma modular forms data for NK^2 <= 1000

* mfdecomp_500.m.txt: Magma output for Nk <= 500 (timings for N=1,2 are bogus)
* mfdecomp_500.gp.txt: gp output for Nk <= 500
* mfdecomp_500.txt : Galois orbit decomposition data for Nk <= 500 (as independently computed by gp and Magma)
* mffield_500.m.txt : Coefficient field data for Nk <= 500 for fields of degree d <= 20 computed in Magma

* mfdecomp_1000.gp.txt gp output for Nk <= 1000
* mfdecomp_1000.txt : Galois orbit decomposition data for Nk <= 1000 (as computed by gp, to be confirmed by Magma)

* mfdecomp_full_100.txt : Galois decomposition data for NK <= 100 computed by Magma with the following format N:k:i:t:[n1,n2,...]:[t1,t2,...]:[f1,f2,...]:[h1,h2,...], where N,k,i,t are as above, [t1,t2,...] is a list of vectors of absolute traces of Hecke eigenvalues a_n for 1<=n<=100 sorted lexicographically (this will match the order of n1,n2,.. because the trace of 1 gives the degree of the coefficient field), [f1,f2,...] is a list of polredbest-stable polynomials defining the coefficient fields for those orbits of dimension <= 20, and [h1,h2,...] is a list of pairs <p,h_p(x)> where p is a prime not dividing N and h_p(x) is the minimal polynomial of T_p (over a cyclotomic field).  The [h1,h2,...] vector only addresses spaces of dimension up to 20, and each list includes p's sufficient to uniquely distinguish each Galois orbit.  All of the vectors that occur are sorted consistently (but note that the last two match prefixes of the first two).

* mfdecomp_full_100.gp.txt : As above but output from gp, excluding the [h1,...]

* mfdata_wt1_500.gp.txt: weight 1, levels 1-500, withh 1000 traces and
  ans. The eigenvalue data field is underdeveloped, only containing
  vectors in Q^d with no basis information (yet).

* data/N1-1000k1 : dimension split for weight 1 forms, all levels to 1000.
* data/N*k* : dimension splits for various weight/level ranges including all with N*k<=1000
* data/all.txt : concatenation of previous
* data/mffield.txt : polynomials for spaces of dimension<=20, N*k<=1000


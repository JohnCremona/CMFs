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

Format of mfdata_B.m.txt is *N:k:i:t:D:T:A:F:C:E:cm:tw:pra:zr:mm:h:X:sd* where B is an upper bound on Nk^2.  The data depends on a degree bound (currently 20), and a coefficient index bound (currently 1000).  The  fields in each record are defined as follows:

 1) N = level, a positive integer
 2) k = weight, a positive integer (for .m.txt files, k > 1)
 3) i = character orbit of chi (Galois orbits of Dirichlet characters chi of modulus N are lex-sorted by order and then by trace vectors [tr(chi(n)) for n in [1..N]], taking traces from Q(chi) to Q; the first orbit index is 1, corresponding to the trivial character, the second orbit will correspond to a quadratic character).
 4) t = time in secs to compute this line of data
 5) D = sorted list of dimensions [d1,d2,...] of Galois stable subspaces of S_k^{new}(N,chi), ordered by dimension
 6) T = lex-sorted list of trace vectors [[tr(a_1),...tr(a_n)],...] for Galois conjugacy classes of eigenforms f corresponding to the subspaces listed in D, traces are from the coefficient field of the form down to Q (note that lex-sorting trace vectors sorts subspaces by dimension because tr(a_1)=tr(1) is the degree of the coefficient field)
 7) A = Atkin-Lehner signs (empty list if chi is not the trivial character (i.e. i=1)) [[<p,sign> for p in Divisors(N)],...], one list of Atkin-Lehner signs for each subspace listed in D.
 8) F = Hecke field polys [[f0,f1,...,1],...] list of coeffs (constant coeff first), one list for each subspace listed in D of dimension up to the degree bound (currently 20); note that F[n] corresponds to the space D[n] but F may be shorter than D
 9) C = Hecke cutters [[<p,[g0,g1,...,1]>,...],...] list of minimal lists of coefficients of kernel polys g_p in T_p sufficient to distinguish all the subspaces listed in D (i.e. the ith form is the unique form lying in the kernel of g_p(T_p) for all the tuples <p,coeffs(g_p)> in the ith list)
10) E = Hecke Eigenvalue data [<g,b,c,d,a,x,m>,...] list of 7-tuples of Hecke eigenvalue data for each subspace listed in D of dimension greater than 1 up to the degree bound where:
      1) g is a list of coefficients of a polredbestified field poly for the Hecke field K (should match entry in F),
      2) b is a list of lists of rationals specifying a basis for the Hecke ring R:=Z[a_n] in terms of the power basis for g
      3) c is an integer that divides the index [O_K:R] of the Hecke ring R in the ring of integers O_K of the Hecke field
      4) d is a pair <disc,fac> where disc is the discriminant of O_K (0 if not known) and fac=[<p,e>,...] is its factorization.
      5) a is a list of lists of integers encoding eigenvalues in terms of the basis b
      6) x is a pair <u,v> where u lists integers generating (Z/NZ)* and v lists of values of chi on u in basis b
      7) m is the least integer such that the coefficients a_1,...,a_m generate the Hecke ring (as a ring)
11) cm = list of pairs <proved,discs> where proved=0,1 and discs is a list of 0, 1, or 3 fundamental discriminants (for k > 1 there is at most 1 and it is a negative discriminant), one pair for each subspace listed in D
12) tw = list of lists of quadrauples <proved,n,m,o> where proved=0,1, n >=1 is a multiplicity, and m and o identify a Galois orbit of a characters [phi] of modulus m for which the corresponding form admits n distinct non-trivial inner-twist by characters in xi in [phi], one list for each subspace up to degree bound. All self-twists are guaranteed to be included, but quadruples with proved=0 could in principal be false positives.
13) pra = list of boolean values (0 or 1) such that pra[i] is 1 if F[i] is the polredabs polynomial for the Hecke field
14) zr = list of proportions of zero a_p over primes p < 2^13 (decimal number), one for each subspace
15) mm = list of list of moments of normalized a_p over primes p < 2^13 (decimal numbers), one for each subspace
16) h = list of trace hashes (linear combination of tr(a_p) over p in [2^12,2^13] mod 2^61-1), one for each subspace of dimension up to the degree bound (not yet present for weight 1)
17) X = list of pairs <u,v>, one for each entry in F, where u is a list of integer generators for (Z/NZ)* and v is a list of lists of rationals specifying corresponding values of chi in the Hecke field in terms of the power basis for F[i].
18) sd = list of boolean values (0,1), one for each subspace in D indicating whether the subspace is self-dual (meaning the a_n are real-valued)
19) eap = list of lists of lists of embedded ap's, one for each subspace in D of dimension greater than the degree bound, currently only used for trivial character (so embedded ap's are real numbers) and Nk^2 > 4000.  For each subspace of dimension d there are d lists of embedded ap's [a_2,a_3,...] (for p < 3000 when 4000 < Nk^2 <= 40000)

Format of mfdecomp_xxx_m.txt and mfdecomp_xxx_gp.txt files is N:k:i:t:D where N is the level, k is the weight, i is the index of the Dicihlet character orbit (sorted in reverse lex order of trace value vectors), t is cpu-time, and D=[n1,n2,...] is a sorted list of Q-dimensions of the minimal Galois stable subspaces of S_k^new(N,chi).

Format of mffield_xxx_m.txt is N:k:i:[n1,n2,...]:[f1,f2,...] where N,k,n1,n2,... are as in mfdecomp_xxx.m.txt and f1,f2,... are lists of integer coefficients of polredbest polynomials defining the coefficient fields (constant coefficient first) for the orbits of dimension at most 20 (so list of f's may be shorter than the list of n's).  Spaces for which the list of field polys would be empty (because the space contains no orbits of dimension at most 20) are omitted.

* mfdata_100.m.txt : Magma modular forms data for Nk^2 <= 100
* mfdata_500.m.txt : Magma modular forms data for NK^2 <= 1000
* mfdata_1000.m.txt : Magma modular forms data for NK^2 <= 1000

* mfdecomp_500.m.txt: Magma output for Nk <= 500 (timings for N=1,2 are bogus)
* mfdecomp_500.gp.txt: gp output for Nk <= 500
* mfdecomp_500.txt : Galois orbit decomposition data for Nk <= 500 (as independently computed by gp and Magma)

* mfdecomp_1000.gp.txt gp output for Nk <= 1000
* mfdecomp_1000.txt : Galois orbit decomposition data for Nk <= 1000 (as computed by gp, to be confirmed by Magma)

* mfdecomp_full_100.m.txt : Galois decomposition data for NK <= 100 computed by Magma with the following format N:k:i:t:[n1,n2,...]:[t1,t2,...]:[f1,f2,...]:[h1,h2,...], where N,k,i,t are as above, [t1,t2,...] is a list of vectors of absolute traces of Hecke eigenvalues a_n for 1<=n<=100 sorted lexicographically (this will match the order of n1,n2,.. because the trace of 1 gives the degree of the coefficient field), [f1,f2,...] is a list of polredbest-stable polynomials defining the coefficient fields for those orbits of dimension <= 20, and [h1,h2,...] is a list of pairs <p,h_p(x)> where p is a prime not dividing N and h_p(x) is the minimal polynomial of T_p (over a cyclotomic field).  The [h1,h2,...] vector only addresses spaces of dimension up to 20, and each list includes p's sufficient to uniquely distinguish each Galois orbit.  All of the vectors that occur are sorted consistently (but note that the last two match prefixes of the first two).

* mfdecomp_full_100.gp.txt : As above but output from gp, excluding the [h1,...]

* mfdata_wt1_500.gp.txt: weight 1, levels 1-500, withh 1000 traces and
  ans. The eigenvalue data field is underdeveloped, only containing
  vectors in Q^d with no basis information (yet).

* data/N1-1000k1 : dimension split for weight 1 forms, all levels to 1000.
* data/N*k* : dimension splits for various weight/level ranges including all with N*k<=1000
* data/all.txt : concatenation of previous
* data/mffield.txt : polynomials for spaces of dimension<=20, N*k<=1000


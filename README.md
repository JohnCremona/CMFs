CMFs
===

code and data for computing Classical Modular Forms in Pari/gp, Magma,
Sage

Code
-------

karim.gp: Karim Belabas's original function
* mf.gp: defines the DecomposeSpaces() funtion in gp
* mf.m: defines the DecomposeSpaces() and ComputeCoefficientFields() funtions in Magma
* mf.py: Python (Sage) scripts for reading and comparing output from DecomposeSpaces()
* polredabs.spec defines Magma interface to polredabs and polredbest
* conrey.m: functions for converting between Galois orbits of Dirichlet characters and Conrey labels of Dirichlet characters

Data
-------

Format of mfdecomp_xxx_m.txt and mfdecomp_xxx_gp.txt files is N:k:i:t:[n1,n2,...] where N is the level, k is the weight, i is the index of the Dicihlet character orbit (sorted in reverse lex order of trace value vectors), t is cpu-time, and [n1,n2,...] is a sorted list of Q-dimensions of the minimal Galois stable subspaces of S_k^new(N,chi)

* mfdecomp_100_10.m.txt: Magma output levels 1-100, weights 2-10 (this data is incorrect due to bug/inconsitency in magma!)
* mfdecomp_100_10.gp.txt: gp output levels 1-100, weights 2-10

* mfdecomp_500.m.txt: gp output for Nk <= 500 (corrects inconsistency in mfdecomp_100_10 files, timings for N=1,2 are bogus)
* mfdecomp_500.gp.txt: Magma output for Nk <= 500
* mfdecomp_500.txt : Galois orbit decomposition data for Nk <= 500 (as independently computed by gp and Magma)
* mffield_500.m.txt : Coefficient field data for Nk <= 500 for fields of degree d <= 20 computed in Magma (newform spaces with no such fields are omitted, polys lised as integer coefficient vectors of polredbest defining polys)

* mfdecomp_1000.gp.txt gp output for Nk <= 1000
* mfdecomp_1000.txt : Galois orbit decomposition data for Nk <= 1000 (as computed by gp, to be confirmed by Magma)




A live version of the code in this PR is available [here](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/).

# Extent and size

### Boxes
Rather than choosing *N* and *k* in boxes, we organize by *Nk²*, which is asymptotically proportional to the [analytic conductor](http://cmfs.lmfdb.xyz/knowledge/show/mf.elliptic.analytic_conductor) of the newform (a good measure of its complexity).  Our tabulation is [complete](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/Completeness) within the following ranges

* *Nk²* ≤ 4000
* *Nk²* ≤ 40000, *χ*=1
* *Nk²* ≤ 40000, *N* ≤ 24
* *Nk²* ≤ 14400, *N* ≤ 100, *k* ≤ 12
* *Nk²* ≤ 100000, *N* ≤ 10
* *Nk²* ≤ 40000, *k* > 1, dimension ≤ 50
These boxes were chosen to include everything currently in the LMFDB and other existing tables of modular forms.

### Counts
* 338,551 nonzero newspaces *S<sub>k</sub>(N, χ)* with trace data (52,531 nonzero)
* 281,219 Galois orbits of newforms (48,688 with rational coefficients, 19,306 of weight 1)
* 14,398,359 complex embedded newforms

### Database size
* 325 GiB of embedded modular forms (*q*-expansions in ℂ)
* 123 GiB of trace data (traces of *q*-expansions down to ℚ)
* 45 GiB of portraits (complex graphs of *q*-expansions)
* 2 GiB of exact *q*-expansion data (when dimension is at most 20)

### Computation time
We spent 20-30 CPU years this fall and winter computing the above data.

### Representation
Exact coefficients are stored using either a [sparse cyclotomic representation](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/1620/1/bp/a/) or in terms of an [LLL-reduced basis for the coefficient ring](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/6877/2/a/s/).  We have exact coefficients in weight 1 or if the dimension is at most 20.

We compute complex *q*-expansions for all embeddings into the complex numbers, even when the dimension is [large](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/983/2/c/a/).

### [Reliability and Rigor](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/Reliability)
Many computations were duplicated in Magma and Pari, providing a check for their correctness.  We also compared with complex analytic data independently computed by Jon Bober, with William Stein's modular form tables and Alan Lauder and Kevin Buzzard's weight 1 tables.  Finally, we have written a verification module for the LMFDB and run various tests on the data.

We have rigorously verified self twists and projective image types in all cases, and inner twists and analytic ranks in most cases.  Any values that are not rigorously computed are explicitly identified.

# User interface
We have rewritten the front end through which a visitor to the LMFDB interacts with classical modular forms, along with many other changes to the LMFDB display code (220 changed files with 14,739 additions and 14,479 deletions).

### Searches
* You can obtain a list of [newforms](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/?search_type=List) or of [newspaces](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/?search_type=Spaces) satisfying various constraints (e.g. [rational forms](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/?dim=1&search_type=List)).
* You can view dimensions of [newforms](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/?search_type=Dimensions) or of [newspaces](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/?weight=2-&dim=1-&search_type=SpaceTraces) in a table organized by *N* and *k*.  You can add constraints and change the ranges of *N* and *k* displayed.
* You can browse [newforms](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/?weight=2-&search_type=Traces) and [newspaces](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/?weight=2-&dim=1-&search_type=SpaceTraces) using a searchable table of traces for their *q*-expansions, that can be used both integer and mod-p modes.  An application: if you know a curve is modular, you can pin down an associated newform by looking at the trace table at small primes.  Counting points mod p is easy, but computing Euler factors is hard in high genus.
* You can get a random form satisfying specificed constraints (e.g. [CM with level a power of 2](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/?level_primes=2&cm=yes&search_type=Random)).
* [Search results](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/?dim=1-&num_forms=10-&char_order=1&search_type=Spaces) for spaces include decomposition into newforms and into Atkin-Lehner eigenspaces.

### Browse
The [front page](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/) includes a curated lists of interesting newforms and newspaces with hovertext describing why these forms and spaces were chosen

### Statistics
We've added [statistics](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/stats), as well as a new dynamic statistics feature allowing you to view custom statistics (e.g. statistics on [weight and level for forms with CM](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/dynamic_stats?cm=yes&col1=level&buckets1=1%2C2-10%2C11-100%2C101-1000%2C1001-2000%2C2001-4000%2C4001-6000%2C6001-8000%2C8001-10000&totals1=yes&proportions=recurse&col2=weight&buckets2=1%2C2%2C3%2C4%2C5-8%2C9-16%2C17-32%2C33-64%2C65-316&totals2=yes&search_type=DynStats))

### Downloads
Downloads are now more broadly available, and you can download various things from homepages (trace forms, *q*-expansions, all stored data) and from search results.

We give linear operators on *S<sub>k</sub>*(*N*, *χ*), expressed as polynomial expressions of Hecke operators, so that the newform is the intersection of their kernels.  This can sometimes speed up construction of the newform in Magma.

### Form homepages
* *q*-expansions are more readable due to changes in representation.  Defaults to showing 10 coefficients, expandable to 100 coefficients on the page, 1000+ coefficients available for download.
* trace expansions are also shown, even when the dimension is [large](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/983/2/c/a/)
* include projective image type for weight 1 forms, including [A₄](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/124/1/i/a/), [S₄](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/148/1/f/a/), [A₅](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/1763/1/p/b/), [D₂](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/3600/1/e/a/) and [large dihedral](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/3997/1/cz/a/).  You can also search for forms with a specified type.
* Matched [weight 1 forms](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/385/1/q/b/) with [Artin representations](http://cmfs.lmfdb.xyz/ArtinRepresentation/2.5_7_11.6t5.1c1) when present in the LMFDB
* include Sato-Tate groups for all newforms of weight larger than 1
* include provable analytic ranks (e.g. [rational form of weight 42](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/2/42/a/a/) and [form of weight 14 with analytic rank 1](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/8/14/b/a/))
* include CM/RM fields for newforms with [self twists](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/39/1/d/a/)
* include [inner twists](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/1089/1/r/a/) for twists by characters that yield other forms in the same Galois orbit
* for forms with exact *q*-expansions, we provide the [values of the character](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/630/2/bv/c/) in the same representation
* We have portraits for both newforms and newspaces, giving plots of the trace form on the Poincare disc.
* change in label scheme but we support [old labels](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/10/8/1/a)

### Embedded form homepages
* There are now [homepages](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/983/2/c/a/472/35/) for newforms equipped with an embedding of the coefficient field into the complex numbers.  They are linked to from the tables of embeddings on each newform page.
* q-expansions are shown with complex coefficients, we include links to the dual form (complex conjugate).
* Coefficients (in both arithmetic and analytic normalizations) and Satake angles are viewable up through n=1000, with more sometimes available for download in high level.

### Space homepages
* We give decompositions of[ *S<sub>k</sub>*<sup>new</sup>(*N*, *χ*) into newforms](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/9075/2/a/), of [*S<sub>k</sub>*<sup>new</sup>(Γ₁(*N*)) into newspaces](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/9075/2/) and *S<sub>k</sub>*<sup>old</sup>(*N*, *χ*) and *S<sub>k</sub>*<sup>old</sup>(Γ₁(*N*)) into lower level pieces.
* Give dimensions for new and old, Eisenstein and cuspidal subspaces
* Show the trace form
* Give bounds on how many a_n are needed to distinguish newforms within a space.  In addition to the standard Sturm bound, we also provide a computed trace bound based on the forms that actually occur.

### L-functions
* both arithmetic and analytic normalizations are available
* We have computed analytic ranks for all of the new L-functions, and proved most of them.
* We compute [Euler factors](http://cmfs.lmfdb.xyz/L/ModularForm/GL2/Q/holomorphic/5/27/c/a/) at all primes up to 100
* zeros on critical line have more precision and are stored in the database rather than computed on the fly, making it easier to find connections to other objects in the LMFDB
* change in label scheme but we support old labels

# Experimental features

We have used classical modular forms as a testing ground for some new features which are applicable to other areas of the LMFDB.

* There is now a verification module to add consistency checks for data in Postgres; you can access it by `from lmfdb.verify import db` and then running either `db.verify` or `db.tablename.verify`.  See the Postgres_FAQ for more details.
* See the description of [dynamic statistics](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/dynamic_stats?cm=yes&col1=level&buckets1=1%2C2-10%2C11-100%2C101-1000%2C1001-2000%2C2001-4000%2C4001-6000%2C6001-8000%2C8001-10000&totals1=yes&proportions=recurse&col2=weight&buckets2=1%2C2%2C3%2C4%2C5-8%2C9-16%2C17-32%2C33-64%2C65-316&totals2=yes&search_type=DynStats) above.
* A variant on knowls used when displaying very long mathematical content.  You can see the results in the *q*-expansions, basis descriptions, coefficient fields and Hecke kernels for some [high weight newforms](http://cmfs.lmfdb.xyz/ModularForm/GL2/Q/holomorphic/2/218/a/b/) and in various other places on classical modular form pages.
* Some nice features for [2-d tables](http://modularform/GL2/Q/holomorphic/?level=1-150&search_type=Dimensions): sticky headers and rotated labels.  They're currently implemented in a somewhat ad-hoc manner, but can be abstracted if more widely used.
* You can change the sort order on search results
* The ability to get a random object satisfying search constraints
* Multiple search result views (e.g. trace tables, dimension tables)
* There is more modularity in the templates, allowing the same search interface to be used on multiple pages

# Mongo to Postgres
While working on classical modular forms, we've fixed various issues with the transition from Mongo to Postgres, and eliminated the last dependencies on Mongo.  One interface change to be aware of is that you now run `from lmfdb import db` to access the database object, rather than `from lmfdb.db_backend import db`.

One change particularly useful for those of you not at MIT is that we tried to reduce the number of queries to the server when possible.  In particular, at startup and when fetching knowl titles we switch to a single database query and cache the results for 10 seconds.

# Issues resolved

This pull request resolves the following issues.

* Weight 1 cusp forms #437
* L-functions for modular forms should be in database #439
* Data quality for classical modular forms #460
* Dual L-function #617
* Make user adjust Fourier coefficient embeddings #653
* Make pretty coefficients #654
* Create separate page for each embedding of a newform #659
* Table options for old/new/CM #674
* Determine planned extent of classical modular forms #873
* Source and extent of data for classical modular forms #1224
* For imprimitive genus 2 L-functions, give links to factors #1227
* Fix errors in classical modular form data and verify its correctness #1248
* Tests for lcalc files #1257
* Modular form history #1282 (we decided not to link it)
* Search by analytic rank #1362
* Plots of modular forms #1408
* Random modular form #1434
* Product L-functions for modular forms #1443
* Sever error on classical modular form pages #1533
* Resource intensive L-function zeros pages for classical modular forms #1680
* Classical modular forms Gamma1(49) weight 3 #1991
* Add Bober's modular form data #2196
* no data for level = 100, k 7, chi = 99 #2340
* Request for documentation on modular form web pages #2630
* Hecke operators, cosets in subset not subgroup #2631
* Debounce knowl clicking #2687 (this is a PR, that we closed)
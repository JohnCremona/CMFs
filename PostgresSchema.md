Spaces
======

Table name: `mf_newspaces`.

This table represents (Galois orbits of) spaces of newforms `S_k^{new}(N, [\chi])`, where `\chi` is a Dirichlet character of modulus N and `[\chi]` denotes its conjugacy class under the action of G_Q.  Orbits are sorted by order and traces of values on [1..N] (lexicographically), so that 1 is the index of the orbit of the trivial character.

Column | Type | Notes
-------|------|------
label | text | (N.k.i)
level | integer | the level N of the modular form
level_radical | integer | product of prime divisors of N
level_primes | jsonb | list of primes divisors of N
weight | smallint | the weight k of the modular form
odd_weight | boolean | whether k is odd
analytic_conductor | double precision | N*(2*Exp(Psi((1+k)/2)))^2 where Psi(t) := Gamma'(t)/Gamma(t)
Nk2 | integer | N*k^2
char_orbit | integer | the index i of the galois orbit of the character for this space.  Galois orbits of Dirichlet characters of modulus N are sorted by the character order and then lexicographically by traces (to Q) of values on 1...N-1.  
char_orbit_label | text | string encoding the char_orbit i via 1->a, 2->b, ... 26->z, 27->ba,... (note the shift, a is 1 not 0).
char_labels | jsonb | Sorted list of Conrey indexes of characters in this Galois orbit
char_order | integer | the order of the character
char_conductor | integer | Conductor of the Dirichlet character
prim_orbit | integer | char_orbit for the primitive version of this character
char_degree | integer | the degree of the (cyclotomic) character field
char_parity | smallint | 1 or -1, depending on the parity of the character
char_is_real | boolean | whether the character takes only real values (trivial or quadratic)
char_values | jsonb | quadruple <N,n,u,v> where N is the level, n is the order of the character, u is a list of generators for the unit group of Z/NZ, and v is a corresponding list of integers for which chi(u[i]) = zeta_n^v[i]
sturm_bound | integer |
trace_bound | integer | the integer n so that the traces from 1 up to n distinguish all forms in this space (e.g. 1 if the dimensions are all distinct)
dim | integer | Q-dimension of this newspace
num_forms | smallint | number of Hecke orbits (each corresponds to a Galois conjugacy class of modular forms)
hecke_orbit_dims | jsonb | Sorted list of dimensions of Hecke orbits (irreducible Galois stable subspaces)
eis_dim | integer | Q-dimension of the eisenstein subspace of the corresponding `M_k(N, \chi)`
eis_new_dim | integer | Q-dimension of the new eisenstein subspace of the corresponding `M_k(N, \chi)`
cusp_dim | integer | Q-dimension of the cuspidal space `S_k(N, \chi)`
mf_dim | integer | Q-dimension of `M_k(N, \chi)`
mf_new_dim | integer | Q-dimension of the new subspace of `M_k(N,\chi)`
AL_dims | jsonb | For spaces with trivial character, this is a lists of triples [AL_eigs,d.n], where AL_eigs is a list of pairs [p,ev] where p is a prime dividing N and ev=+/-1 is an Atkin-Lehner eigevnalue at p, while d and n record the total dimension and number of newforms that lie in the intersection of the corresponding eigenspaces.
plus_dim | integer | For spaces with tirival character, dimension of the subspace with Fricke-eigevalue +1

Table name: `mf_newspace_portraits`

Column | Type | Notes
-------|------|------
label | text | label (N.k.i) of the newspace
portrait | text | base-64 encoded image of the newspace (plot created by portrait.sage) to display in the properties box

Table name: `mf_subspaces`.

This table represents embeddings of newspaces at level M into cusp spaces at level N (these will be old at level N except when M=N).

Column | Type | Notes
-------|------|------
label | text | label N.k.i for the cuspidal space `S_k(N, [\chi])` (same as the label for `S_k^{new}(N, [\chi])`)
level | integer | level N of the cuspidal space `S_k(N, [\chi])`
weight | smallint | weight k of the cuspidal space `S_k(N, [\chi])`
char_orbit_index | integer | index i of the character orbit `[\chi]` in the sorted list of character orbits of modulus N
char_orbit_label | text | base-26 encoding (1='a') of index i of the character orbit that appears in label
char_labels | jsonb | list of Conrey indexes n of the characters N.n in the Galois orbit indexed by i
dim | integer | dimension of `S_k(N, [\psi])`
sub_label | text | The label of the newspace `S_k^{new}(M, [\psi])` that appears as a non-trivial subspace of`S_k(N, [\chi])`
sub_level | integer | (M)
sub_char_orbit_index | integer | index j of `[\psi]` in sorted list of character orbits of modulus M
sub_char_orbit_label | text | base-26 encoding (1='a') of index j of the subspace character orbit that appears in sub_label
sub_char_labels | jsonb | list of Conrey indexes n of the characters M.n in the Galois orrbit indexed by j.
sub_dim | integer | the dimension of `S_k^{new}(M, [\psi])`
sub_mult | integer | Multiplicity of`S_k^{new}(M, [\psi])` as a direct summand of `S_k(N, [\chi])` (this is just the number of divisors of N/M).  Summing dimensions of embedded newspaces with multiplicity gives the dimension of the cusp space.

Table name: `mf_gamma1_subspaces`.

Column | Type | Notes
-------|------|------
label | text | label N.k for the cuspidal space `S_k(Gamma1(N))`
level | integer | level N of the cuspidal space S_k(Gamma_1(N))
weight | smallint | weight k of the cuspidal space S_k(Gamma_1(N))
dim | integer | dimension of S_k(Gamma_1(N))
sub_level | integer | level M of the newspace S_k^{new}(Gamma_1(M)) that embed in S^k(Gamma_1(N))
sub_dim | integer | dimension of S_k^{new}(Gamma_1(M))
sub_mult | integer | multiplicity of S_k^{new}(Gamma_1(M)) as a direct summand of S_k^{Gamma_1(N)).  Summing dimensions of embedded newspaces S_k^{new}(Gamma_1(M)) with multiplicity gives the dimension of the cusp space S_k(Gamma_1(N).

Table name: `mf_gamma1_portraits`.

Column | Type | Notes
-------|------|------
label | text | label N.k for the cuspidal space `S_k(Gamma1(N))`
portrait | text | base-64 encoded image of the newspace (plot created by portrait.sage) to display in the properties box


Newforms
========

Table name: `mf_newforms`

Column | Type | Notes
-------|------|------
label |  text | (N.k.i.x)
space_label | text | (N.k.i)
level | integer | the level N of the modular form
level_radical | integer | product of prime divisors of N
level_primes | jsonb | list of prime divisors of N
weight | smallint | the weight k of the modular form
odd_weight | boolean | whether k is odd
analytic_conductor | double precision | N*(2*Exp(Psi((1+k)/2)))^2 where Psi(t) := Gamma'(t)/Gamma(t)
Nk2 | integer | N*k^2
char_orbit_index | integer | The index i of the Galois orbit of this form in the sorted list of character orbits, as described above.
char_orbit_label | text | string encoding i (with a=1).
char_conductor | integer | Conductor of the Dirichlet character
prim_orbit_index | integer | char_orbit for the primitive version of this character
char_order | integer | the order of the character
char_labels | jsonb | Sorted list of Conrey indexes of characters in this Galois orbit
char_degree | integer | Degree of the (cyclotomic) character field
char_parity | smallint | 1 or -1, depending on the parity of the character
char_is_real | boolean | whether the character takes only real values (trivial or quadratic)
char_values | jsonb | quadruple <N,n,u,v> where N is the level, n is the order of the character, u is a list of generators for the unit group of Z/NZ, and v is a corresponding list of integers for which chi(u[i]) = zeta_n^v[i]hecke_orbit | integer | (X) An integer that is encoded into x in the label via 1=a, 2=b, 26=z, 27=ba, 28=bb.  Note the shift: the letter is the Cremona code for X-1.
hecke_orbit_code | bigint | encoding of the tuple (N.k.i.x) into 64 bits, used in eigenvalue tables.  N + (k<<24) + ((i-1)<<36) + ((X-1)<<52).
dim | integer | the dimension of this Hecke orbit
field_disc | numeric | discriminant of the coefficient field, if known
field_poly | jsonb | list of integers giving defining polynomial for the Hecke field (standard Sage order of coefficients)
field_poly_is_cyclotomic | boolean | true if field_poly is a cylcotomic polynomial (the field might be Q(zeta_n) even when this flage is not set if we haven't chosen a cyclotomic polynomial to define it)
field_poly_is_real_cyclotomic | boolean | true if field_poly is the minimal polynomial of zeta_n + zeta_n^-1 for some n (the field might be Q(zeta_n)^+ even when this flage is not set if we haven't chosen a cyclotomic polynomial to define it)
field_poly_root_of_unity | integer | the value of n if either field_poly_is_cylotomic of field_poly_is_real_cyclotomic is set
is_polredabs | boolean | whether the polynomial has been reduced by Pari's `polredabs`
nf_label | text | LMFDB label for the corresponding number field (can be NULL)
is_self_dual | boolean | true if L-func is self-dual (coeff field is totally real)
hecke_ring_numerators | jsonb | List of lists of integers, giving the numerators of a basis for the Hecke order in terms of the field generator specified by the field polynomial
hecke_ring_denominators | jsonb | List of integers, giving the denominators of the basis
hecke_ring_generator_nbound | integer | minimal integer m such that a_1,...,a_m generate the Hecke ring
hecke_ring_inverse_numerators| jsonb | List of lists of integers, giving the numerators of the inverse basis that specifies powers of nu in terms of the betas
hecke_ring_inverse_denominators | jsonb | List of integers, giving the denominators of the inverse basis
hecke_ring_index | numeric | (a divisor of) the index of the order generated by the Hecke eigenvalues in the maximal order.
hecke_ring_index_factorization | jsonb | Factorization of hecke_ring_index stored as a list of pairs [p,e].
hecke_ring_index_proved | boolean | whether the index has been proved correct (computing the maximal order may not be possible)
hecke_ring_power_basis | boolean | true if the matrix specified by hecke_ring_numerators and hecke_ring_denominators is the identity matrix
hecke_ring_cyclotomic_representation | boolean | true if elements of the hecke ring are specified as sums of powers of zeta_n of degree up to n-1 (used only for weight 1 forms).  If this is set either field_poly_is_cyclotomic or field_poly_is_real_cyclotomic will also be set and field_poly_root_of_unity gives the value of n
hecke_ring_character_values | jsonb | list of pairs [[m1,[a11,...a1n]],[m2,[a12,...,a2n]],...] where [m1,m2,...,mr] are generators for Z/NZ and [ai1,...,ain] is the value of chi(mi) expressed in terms of the Hecke ring basis or in cyclotomic representation
trace_hash | bigint | linear combination of the a_p between 2^12 and 2^13 reduced mod 2^61-1 as defined in BSSVY, only guaranteed for wt > 1 and dim <= 20
trace_zratio | double precision | proportion of zero a_p values for p <= 2^13 (rounded to three decimal places)
trace_moments | jsonb | list of moments of a_p/p^((k-1)/2) computed over p <= 2^13 (rounded to three decimal places)
qexp_prec | smallint | n so that q-expansion is known to precision O(q^n).
related_objects | jsonb | list of text URLs of related objects (e.g. elliptic curve isogeny class, Artin rep, ...), e.g. ["EllipticCurve/Q/11/a"]
analytic_rank | smallint |
analytic_rank_proved | boolean | true if analytic rank is provably correct (it is always an upper bound)
self_twist_type | smallint | 0=none, 1=cm, 2=rm, 3=both
is_self_twist | boolean | whether this form is a self twist
is_cm | boolean | whether the form has CM
is_rm | boolean | whether the form has RM
self_twist_discs | jsonb | list of discriminants giving self twists (either 0,1,or 3 quadratic discriminants)
cm_discs | jsonb | list of CM discriminants (the negative discriminants listed in self_twist_discs)
rm_discs | jsonb | list of RM discriminants (the positive discriminants listed in self_twist_discs)
self_twist_proved | boolean | whether the self twists have been proved unconditionally
is_twist_minimal | boolean |
inner_twist | jsonb | List of quadruples <b,m,M,o> where <M,o> identifies the Galois orbit if a Dirichlet character, m is the number of characters in this orbit that give rise to an inner twist, and b is 1 if the inner twists is proved.  All inner twists are guaranteed to be included in the list, but those without proved set could be false positives.
inner_twist_count | integer | number of inner twists (includes proved and unproved), null if inner twists have not been computed (this applies to all forms of dimension > 20 and weight > 1)
atkin_lehner_eigenvals | jsonb | a list of pairs [p, ev] where ev is 1 or -1, the Atkin-Lehner eigenvalue for each p dividing N (NULL overall if nontrivial character, an empty list for level 1 and trivial character)
atkin_lehner_string | text | list of signs +/- of Atkin-Lehner eigenvalues ordered by p (facilitates lookups)
fricke_eigenval | smallint | product of the Atkin-Lehner eigenvalues (NULL if nontrivial character)
hecke_cutters | jsonb | a list of pairs [p, F_p] where F_p is a list of integers encoding a polynomial; the intersection of the kernels of F_p(T_p) is this Hecke orbit
qexp_display | text | latexed string for display on search page results
trace_display | jsonb | list of traces tr(a_2), tr(a_3), tr(a_5), tr(a_7) for display on search page results
traces | jsonb | full list of traces tr(a_n) for n from 1 to 1000
projective_image_type | text | for weight 1 forms, one of "Dn", "A4", "S4", "A5"
projective_image | text | for weight 1 forms, isomorphism class of project image (e.g. which Dn)
projective_field | jsonb | for weight 1 forms, list of integer coefficients of polynomial whose splitting field is the fixed field of the kernel of the projective Galois rep (subfield of the artin field fixed be the center of its Galois group)
projective_field_label | text | LMFDB label of projective field (if present)
artin_degree | integer | for weight 1 forms, order of the image of the Galois rep, equivalently, the degree of the Artin field
artin_image | text | for weight 1 forms, small group label of the image of the Galois rep (and the Galois group of the artin field)
artin_field | jsonb | for weight 1 forms, list of integer coefficients of polynomial whose splitting field is the fixed field of the Galois rep (equivalently, a defining polynomial for the 2-dim Artin rep corresponding to this weight 1 form)
artin_field_label | text | LMFDB label of artin field (if present)

Table name: `mf_newform_portraits`

Column | Type | Notes
-------|------|------
label | text | label (N.k.i.x) of the newform
portrait | text | base-64 encoded image of the newform (plot created by portrait.sage) to display in the properties box

Hecke eigenvalues
=================

Table name: `mf_hecke_nf`

Column | Type | Notes
-------|------|------
hecke_orbit_code | bigint | encoding of the tuple (N.k.i.x) into 64 bits
n | integer |
an | jsonb | list of integers, giving the Hecke eigenvalue as a linear combination of the basis specified in the orbit table
trace_an | numeric | trace of a_n down to Z

Table name: `mf_hecke_cc`

Column | Type | Notes
-------|------|------
hecke_orbit_code | bigint | encoding of the tuple (N.k.i.x) into 64 bits
lfunction_label | text | (N.k.c.x.n) where N.c is the Conrey label of the restriction to the cyclotomic field and n enumerates the embeddings with the same character (starting at 1)
conrey_label | integer | the Conrey label for the restriction of the embedding to the character field
embedding_index | integer | enumeration of which embedding (shows up in L-function link) for the given conrey label
embedding_m | integer | enumeration of which embedding over all conrey labels in the specified hecke orbit.  Ordering is the same as lexicographic on (conrey_label, embedding_index).  1-indexed.
embedding_root_real | double precision | real part of the root corresponding to this embedding
embedding_root_imag | double precision | imaginary part of the root corresponding to this embedding
an | array | list of pairs [x,y] of doubles x, y so that `a_n = x + iy` for `n \in [1,1000]`
angles | array | list of `\theta_p`, where '\theta_p' is `Null` if `p` is bad, and for good `p` we have `a_p = p^{(k-1)/2} (e^{2\pi i \theta_p} + chi(p)e^{-2\pi i \theta_p})`; it will range over all primes p < 1000, where `-0.5 < \theta_p <= 0.5`. Furthermore, we store the minimum value of the two options for `\theta_p` in that interval.

Dirichlet characters
====================

Table name: `char_dir_orbits`

Column | Type | Notes
-------|------|------
orbit_label | text | (N.i)
orbit_index | smallint | (i) Index in the list of traces down to Q of the values of all characters of modulus N
modulus | smallint
conductor | smallint
prim_orbit_index | smallint | Index for the primitive version of this conductor
order | smallint
parity | smallint
galois_orbit | jsonb | sorted list of conrey_labels in the same galois orbit
is_real | boolean | if quadratic or trivial
is_primitive | boolean | if modulus = conductor
char_degree | smallint | degree of the cyclotomic field containing the image, ie Euler phi of the order; this is the same as the size of the Galois orbit

Table name: `char_dir_values`

Note that the values in this table are stored as integers m so that the actual value is `e^{2\pi i m/d}` where `d` is the `order`.

Column | Type | Notes
-------|------|------
label | text | N.n where N is the modulus and n is the conrey label
orbit_label | text | N.i where N is the modulus and i is the orbit_index
prim_label | text | the label of primitive character inducing this one
order | smallint
values | jsonb | list of the first twelve values on -1,1, then the next ten integers relatively prime to the modulus
values_gens | jsonb | list of pairs [n, chi(n)] for n generating the unit group

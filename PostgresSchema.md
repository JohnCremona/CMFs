Spaces
======

Table name: `mf_newspaces`.

This table represents (Galois orbits of) spaces of newfors`S_k^{new}(N, [\chi])`, where `\chi` is a Dirichlet character of modulus N and `[\chi]` denotes its conjugacy class under the action of G_Q.  Orbits are sorted by order and traces of values on [1..N] (lexicographically), so that 1 is the index of the orbit of the trivial character.

Column | Type | Notes
-------|------|------
label | text | (N.k.i)
level | integer | (N)
weight | smallint | (k)
odd_weight | bool | whether k is odd
char_orbit_index | integer | (i) Index in the list of traces down to Q of the values of all characters of modulus N, starting at 1.  This is encoded into i in the label via 1=a, 2=b, 26=z, 27=ba, 28=bb.  Note the shift: the letter is the Cremona code for i-1.
char_orbit_label | integer | letter encoded version of (i)
char_labels | jsonb | Sorted list of Conrey indexes of characters in this Galois orbit
char_order | integer | the order of the character
char_conductor | integer | Conductor of the Dirichlet character
prim_orbit_index | integer | char_orbit for the primitive version of this character
char_degree | integer | the degree of the (cyclotomic) character field
char_parity | smallint | 1 or -1, depending on the parity of the character
char_is_real | bool | whether the character
sturm_bound | integer |
trace_bound | integer | the integer n so that the traces from 1 up to n distinguish all forms in this space (e.g. 1 if the dimensions are all distinct)
dim | integer | Q-dimension of this newspace
eis_dim | integer | Q-dimension of the eisenstein subspace of the corresponding `M_k(N, \chi)`
eis_new_dim | integer | Q-dimension of the new eisenstein subspace of the corresponding `M_k(N, \chi)`
cusp_dim | integer | Q-dimension of the cuspidal space `S_k(N, \chi)`
mf_dim | integer | Q-dimension of `M_k(N, \chi)`
hecke_orbit_dims | jsonb | Sorted list of dimensions of Hecke orbits

Table name: `mf_subspaces`.

This table represents embeddings of newspaces at level M into cusp spaces at level N (these will be old at level N except when M=N).

Column | Type | Notes
-------|------|------
label | text | label (N.k.i) for the modular form space `S_k(N, [\chi])` (same as the label for `S_k^{new}(N, [\chi])`)
level | integer | (N)
weight | smallint | (k) (this is the same for all embedded subspaces)
char_orbit | integer | (i) index of `[\chi]` in sorted list of character orbits of modulus N
conrey_labels | jsonb | list of conrey labels in char_orbit
dim | integer | dimension of `S_k(N, [\psi])`
sub_label | text | The label of the newspace `S_k^{new}(M, [\psi])` that appears as a non-trivial subspace of`S_k(N, [\chi])`
sub_level | integer | (M)
sub_char_orbit | integer | (j) index of `[\psi]` in sorted list of character orbits of modulus M
sub_conrey_labels | jsonb | list of Conrey labels for the subspace
sub_dim | integer | the dimension of `S_k^{new}(M, [\psi])`
sub_mult | integer | The number of isomorphic copies of `S_k^{new}(M, [\psi])` in `S_k(N, [\chi])` (this is just the number of divisors of N/M).  Summing dimensions of embedded newspaces with multiplicity gives the dimension of the cusp space.

Table name: `mf_gamma1_subspaces`.

Column | Type | Notes
-------|------|------
level | integer
weight | smallint
dim | integer
sub_level | integer
sub_dim | integer
sub_mult | integer

Newforms
========

Table name: `mf_newforms`

Column | Type | Notes
-------|------|------
label |  text | (N.k.i.x)
space_label | text | (N.k.i)
level | integer | (N)
weight | smallint | (k)
odd_weight | bool | whether k is odd
char_orbit_index | integer | (i) As above
char_orbit_label | integer | letter encoded version of (i)
char_conductor | integer | Conductor of the Dirichlet character
prim_orbit_index | integer | char_orbit for the primitive version of this character
char_order | integer | the order of the character
char_labels | jsonb | Sorted list of Conrey indexes of characters in this Galois orbit
char_parity | smallint | 1 or -1, depending on the parity of the character
char_is_real | bool | whether the character
char_degree | integer | Degree of the (cyclotomic) character field
hecke_orbit | integer | (X) An integer that is encoded into x in the label via 1=a, 2=b, 26=z, 27=ba, 28=bb.  Note the shift: the letter is the Cremona code for X-1.
hecke_orbit_code | bigint | encoding of the tuple (N.k.i.x) into 64 bits, used in eigenvalue tables.  N + (k<<24) + ((i-1)<<36) + ((X-1)<<52).
dim | integer | the dimension of this Hecke orbit
field_poly | jsonb | list of integers giving defining polynomial for the Hecke field (standard Sage order of coefficients)
is_polredabs | boolean | whether the polynomial has been reduced by Pari's `polredabs`
nf_label | text | LMFDB label for the corresponding number field (can be NULL)
hecke_ring_numerators | jsonb | List of lists of integers, giving the numerators of a basis for the Hecke order in terms of the field generator specified by the field polynomial
hecke_ring_denominators | jsonb | List of integers, giving the denominators of the basis
hecke_ring_index | jsonb | (a divisor of) the index of the order generated by the Hecke eigenvalues in the maximal order.  Stored as its factorization, as a list of pairs [p,e].
hecke_ring_index_proven | boolean | whether the index has been proven correct (computing the maximal order may not be possible)
trace_hash | bigint | appropriate linear combination of the a_p between 2^12 and 2^13
qexp_prec | smallint | n so that q-expansion is known to precision O(q^n).
*embeddings* | jsonb | list of pairs (x,y), giving an ordering of the complex roots x+iy of the field poly that define the embedding enumeration (corresponding to the lexicographic ordering of chi, n in the L-function labels) **not present, this should be in separate different table or put in mf_hecke_cc**
isogeny_class_label | text | the isogeny class label of the corresponding elliptic curve or modular abelian variety (could be null if not yet in the database)
analytic_rank | smallint |
is_cm | smallint | whether there is cm.  1=yes, -1=no, 0=unknown
cm_disc | smallint | The (negative) discriminant of the order by which we have CM (0 if no CM)
cm_hecke_char | text | label for the Hecke character giving the CM
cm_proved | boolean | whether the cm columns are provably correct
has_inner_twist | smallint | whether there is an inner twist.  1=yes, -1=no, 0=unknown
is_twist_minimal | boolean |
inner_twist | jsonb | List of integers giving the char_orbit values for the nontrivial Dirichlet characters that give inner twists
inner_twist_proved | boolean | whether the inner twist columns are provably correct
atkin_lehner_eigenvals | jsonb | a list of pairs [p, ev] where ev is 1 or -1, the Atkin-Lehner eigenvalue for each p dividing N (NULL overall if nontrivial character)
hecke_cutters | jsonb | a list of pairs [p, F_p] where F_p is a list of integers encoding a polynomial; the intersection of the kernels of F_p(T_p) is this Hecke orbit
qexp_display | text | latexed string for display on search page results
trace_display | jsonb | list of the first four a_n traces for display on search page results

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
embedding_index | integer | enumeration of which embedding (shows up in L-function link), corresponding to the embeddings list in the orbit table
embedding_root_real | real | real part of the root corresponding to this embedding
embedding_root_imag | real | imaginary part of the root corresponding to this embedding
an | jsonb | list of pairs [x,y] of doubles x, y so that `a_n = x + iy`
angles | jsonb | list of pairs [p, `\theta_p`] where `a_p = p^{(k-1)/2} (e^{2\pi i \theta_p} + chi(p)e^{-2\pi i \theta_p})`; it will range over good primes p, with `\theta_p` between -0.5 and 0.5

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
cyc_degree | smallint | degree of the cyclotomic field containing the image, ie Euler phi of the order; this is the same as the size of the Galois orbit

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

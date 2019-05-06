AttachSpec("mf.spec");

function IsPermutationMatrix(A) return &and[#[a:a in r|a ne 0] eq 1:r in A]; end function;
function IsDiagonalMatrix(A) n := #A; return &and[[j:j in [1..n]|A[i][j] ne 0] eq [i]:i in [1..n]]; end function;

function CoefficientFieldPoly (f, d)
    R<x>:=PolynomialRing(Rationals());
    if d eq 1 then return x; end if;
    a := Coefficients(f);
    assert a[1] eq 1;
    z := 0;
    for i:=2 to #a do
        if a[i] in Integers() then continue; end if;
        z +:= (i-1)*a[i];
        g := AbsoluteMinimalPolynomial(z);
        if Degree(g) eq d then return g; end if;
        assert Degree(g) lt d;
    end for;
    error "Unable to construct the coefficient field of modular form", f;
end function;

function ModularSymbolsDual(M, V)   // copied from modsym.m
   assert V subset DualRepresentation(M); MM := New(ModSym); MM`root := AmbientSpace(M); MM`is_ambient_space := false;
   MM`dual_representation := V; MM`dimension := Dimension(V); MM`sign := M`sign; MM`F := M`F; MM`k := M`k;
   return MM;
end function;

function KernelLinearCombo(I, M)
  //The kernel of I on M, the subspace of M defined as the kernel of sum_i I[i][1]*T_{I[i][2]}.
  cutter := &+[c[2]*DualHeckeOperator(M,c[1]) : c in I];
  W := RowSpace(KernelMatrix(cutter)*BasisMatrix(DualRepresentation(M)));
  N := ModularSymbolsDual(AmbientSpace(M),W);
  return N;
end function;
    
// Given a list of cutters recontstructs the corresponding subspace of modular symbols for the specifiec character chi and weight k
function ReconstructNewspaceComponent(chi,k,cutters:sign:=-1)
    if #cutters gt 0 and Type(cutters[1][2]) eq SeqEnum then
        R<x>:=PolynomialRing(Rationals());
        cutters := [<a[1],R!a[2]>:a in cutters];
    end if;
    return Kernel(cutters,NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,sign))));
end function;

// Given a list of Hecke orbits in a newspace compute a list of cutters that can be used to reconstruct them    
function ComputeHeckeCutters (S)
    num := #S;
    HC := [[]:i in [1..num]];
    if num le 1 then return HC; end if;
    N := Level(S[1]);
    n := 1;  p := 1;
    while true do
        p := NextPrime(p);
        if N mod p ne 0 then
            for i:=1 to num do
                g := Norm(HeckePolynomial(S[i],p));
                A := Factorization(g);  assert #A eq 1; g:=A[1][1];
                Append(~HC[i],<p,Coefficients(g)>);
            end for;
            m := #Set(HC);
            if m eq num then return HC; end if;
            if m eq n then for i:=1 to num do Prune(~HC[i]); end for; else n := m; end if;
        end if;
    end while;
end function;

// No longer needed, used to trime extraneous terms that were erroneously included in an earlier implementation
function MinimizeHeckeCutters (HC)
    num := #HC;
    if num eq 0 then return []; end if;
    if num eq 1 then return [[]]; end if;
    assert #{#c:c in HC} eq 1;
    NHC := [[]:i in [1..num]];
    n := 1;
    for i:= 1 to #HC[1] do
        for j:=1 to num do Append(~NHC[j],HC[j][i]); end for;
        m := #Set(NHC);
        if m eq num then return NHC; end if;
        if m eq n then for j:=1 to num do Prune(~NHC[j]); end for; else n := m; end if;
    end for;
    print "Error, invalid Hecke cutter!";
    assert #Set(HC) eq num;
end function;

// Determines whether newform of character chi, dimension d, with rational traces t and Hecke field defined by f for modular symbol space S is self dual or not
function IsSelfDual (chi,d,t,f,S)
    // trivial character -> totally real coeff field -> self dual (see Ribet's Galreps attached to eigenforms with nebentypus in Antwerp V, Prop 3.2)
    if Order(chi) eq 1 then return true; end if;
    // Otherwise the coeff field is totally imaginary unless the char_order is 2 and chi(p)a_p=a_p for all p
    if Order(chi) gt 2 then return false; end if;
    // if the coeff field has odd degree then it is totally real because it cannot be a cm field (by Ribet Prop 3.2)
    if IsOdd(d) then return true; end if;
    // check if we know that tr(a_p)'s is nonzero at a good prime where chi(p) eq -1 (is so, cannot be self-dual by Ribet Prop 3.3)
    N := Modulus(chi);
    if not &and[t[p] eq 0:p in PrimesInInterval(1,#t)|chi(p) eq -1] then return false; end if;
    if #f eq 0 then
        printf "Unable to determine whether form of dimension %o is self dual or not, Hecke field unspecified, so computing Hecke field...\n", d;
        t := Cputime();
        F:=Eigenform(S,50);
        f:=CoefficientFieldPoly(F,d);  // will fail if 50 is not big enough
        printf "Computed hecke_field of degree %o in %.3os\n", d, Cputime()-t;
    else
        assert #f eq d+1;
    end if;
    return IsTotallyReal(NumberField(PolynomialRing(Rationals())!f));
end function;

// Given a list of a_n for a newform of character chi and weight k returns a list of quadruples <b,n,M,i> where b=0,1 indicates proven results, n is a multiplicity,
// and M,i identifies a Galois orbit [M.i] of primitive characters of modulus M for which the newform admits n distinct inner twists by characters in [M.i]
function InnerTwistData (a,chi,k:CharTable:=AssociativeArray())
    xi,B := InnerTwists(a,chi,k);
    for x in xi do M := Modulus(x); if not IsDefined(CharTable,M) then G,T := CharacterOrbitReps(M:RepTable); CharTable[M] := <G,T>; end if; end for;
    xi := Sort([<M,CharTable[M][2][x],B[j] le #a select 1 else 0, B[j]> where M:=Modulus(x) where x := xi[j] : j in [1..#xi]]);
    return [<x[3],Multiplicity(Multiset(xi),x),x[1],x[2]> : x in Set(xi)];
end function;

function NewspaceTraces (chi, k, o, n: Detail:= 0)
    start := Cputime();
    if Detail gt 0 then printf "Constructing space %o:%o:%o...", Modulus(chi),k,o; t:=Cputime(); end if;
    NS := NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1)));
    if Detail gt 0 then printf "dimension %o, took %o secs\n", QDimension(NS),Cputime()-t; end if;
    T := [];
    for i:=1 to n do
        if Detail gt 0 then printf "Computing trace(a_%o)...",i; t:=Cputime(); end if;
        T[i] := Trace(Trace(HeckeOperator(NS,i)));
        if Detail gt 0 then printf "%o took %o secs\n", T[i],Cputime()-t; end if;
    end for;
    if Detail gt 0 then printf "Total time to compute %o traces for newspace %o:%o:%o was %.3os\n", n, Modulus(chi),k,o,Cputime()-start; end if;
    return T;
end function;

function CompareEmbeddings (f,a,b,prec)
    for n := 2 to Degree(f) do
        ac := Conjugate(Coefficient(f,n),a:Prec:=prec);  bc := Conjugate(Coefficient(f,n),b:Prec:=prec);
        if Real(ac) lt Real(bc) then return -1; end if;
        if Real(ac) gt Real(bc) then return 1; end if;
        if Imaginary(ac) lt Imaginary(bc) then return -1; end if;
        if Imaginary(ac)gt Imaginary(bc) then return 1; end if;
    end for;
    error "Unable to distinguish embeddings!";
end function;

// Given an eigenform f as a power series over a relative extension K/Q(chi) return a list of integers L that permutes the sequence of
// embeddings ordered by [i,j] (where i indexes embeddings of Q(chi) in Magma order and j indexes relative embeddings of K in magma order)
// into the ordering of complex embeddings of f sorted by Conrey label and lex order of a_n (where a_n are compared in re,im lex order)
function SortEmbeddings (f, chi, prec)
    CL := ConreyConjugates(chi,map<Integers()->Codomain(chi)|n:->chi(n)>);  // list of Conrey labels for [chi] ordered by magma embeddings of Q(chi)
    dK := Degree(CoefficientRing(Parent(f)));
    if #CL eq 1 then
        return [j:j in Sort([1..dK],func<a,b|CompareEmbeddings(f,[a],[b],prec)>)];
    end if;
    L := &cat [[[i,j]:j in Sort([1..dK],func<a,b|CompareEmbeddings(f,[i,a],[i,b],prec)>)]:i in Sort([1..#CL],func<a,b|CL[a]-CL[b]>)];
    return [(r[1]-1)*dK+(r[2]-1)+1:r in L];
end function;

/*
Format of data is N:k:i:t:D:T:A:F:C:E:cm:tw:pra:zr:mm:h:X:sd:eap
The data depends on a degree bound (determines forms with exact eigenvalue data, a coefficient count (number of a_n to compute), and a complex precision (for forms without exact eigevnalue data)

N = level, a positive integer
k = weight, a positive integer (for .m.txt files, k > 1)
i = character orbit of chi (Galois orbits of Dirichlet characters chi of modulus N are lex-sorted by order and then by trace vectors [tr(chi(n)) for n in [1..N]], taking traces from Q(chi) to Q; the first orbit index is 1, corresponding to the trivial character, the second orbit will correspond to a quadratic character).
t = time in secs to compute this line of data
D = sorted list of dimensions [d1,d2,...] of Galois stable subspaces of S_k^{new}(N,chi), ordered by dimension
T = lex-sorted list of trace vectors [[tr(a_1),...tr(a_n)],...] for Galois conjugacy classes of eigenforms f corresponding to the subspaces listed in D, traces are from the coefficient field of the form down to Q (note that lex-sorting trace vectors sorts subspaces by dimension because tr(a_1)=tr(1) is the degree of the coefficient field)
A = Atkin-Lehner signs (empty list if chi is not the trivial character (i.e. i=1)) [[<p,sign> for p in Divisors(N)],...], one list of Atkin-Lehner signs for each subspace listed in D.
F = Hecke field polys [[f0,f1,...,1],...] list of coeffs (constant coeff first), one list for each subspace listed in D of dimension up to the degree bound (currently 20); note that F[n] corresponds to the space D[n] but F may be shorter than D
C = Hecke cutters [[<p,[g0,g1,...,1]>,...],...] list of minimal lists of coefficients of charpolys g(x) of T_p sufficient to distinguish all the subspaces listed in D up to the degree bound.
E = Hecke Eigenvalue data [<g,b,n,m,e>,...] list of tuples <g,b,n,m,e> of Hecke eigenvalue data for each subspace listed in D of dimension greater than 1 up to the degree bound where:
    g is a polredbestified field poly for the coefficient field (should be the same as the corresponding poly in F),
    b is a basis for the Hecke ring R:=Z[a_n] in terms of the power basis of K:=Q[x]/(f(x)) (a list of lists of rationals),
    n is an integer that divides the index [O_K:R] of the Hecke ring R in the ring of integers O_K
    m is a boolean (0 or 1) indicating whether or not we know that n is maximal, i.e. n = [Z(f):O_{Q(f)}]
    e is a list of eigenvalues specified in terms of the basis b (list of deg(f) integers for each a_n)
    x is a pair <u,v> where u is a list of integers generating Z/NZ* and v is a list of values of chi on u in written in the basis b
cm = list of cm discriminants, one for each subspace listed in D up to the degree bound, 0 indicates non-CM forms (rigorous)
tw = list of lists of quadruples <b,n,m,i> identifying char orbits m.i of non-trivial inner twists with multiplicity n, b=0,1 indicates proved or not
pra = list of boolean values (0 or 1) such that pra[i] is 1 if F[i] is the polredabs polynomial for the Hecke field
zr = list of proportions of zero a_p over primes p < 2^13 (decimal number), one for each subspace
mm = list of list of moments of normalized a_p over primes p < 2^13 (decimal numbers), one for each subspace
h = list of trace hashes (linear combination of tr(a_p) over p in [2^12,2^13] mod 2^61-1), one for subspace
X = list of pairs <u,v> one for each entry in F where u is a list of integers r generating Z/NZ* and v is a list of values of chi on r in power basis defined by corresponding entry in F
sd = list of booleans, one for each entry in D, indicating whether newform is self dual or not (i.e. a_n are real)
eap = list of lists of lists of real or complex valued a_p's for p up to the coefficient bound for each embedding of each form where exact eigenvalues have not been computed
      if character is trivial embedded a_p's will always be real (this is actually the only case currently used)
*/

function NewspaceData (chi, k, o: CharTable:=AssociativeArray(), TraceHint:=[], DimensionsOnly:=false, ComputeEigenvalues:=false, ComputeTwists:=false, ComputeTraceStats:=false,
                       NumberOfCoefficients:=0, DegreeBound:=0, EmbeddingPrecision:= 0, Detail:=0, ReturnDecomposition:=false, ComputeCutters:=false, SelfTwistBound:=0)
    start := Cputime();
    N := Modulus(chi);
    dNS := QDimensionNewCuspForms(chi,k);
    if dNS eq 0 then
        if Detail gt 0 then printf "The space %o:%o:%o is empty\n",N,k,o; end if;
        s := Sprintf("%o:%o:%o:%o:[]", N, k, o, Cputime()-start);
        if not DimensionsOnly then s cat:= ":[]:[]:[]:[]:[]:[]:[]:[]:[]:[]:[]:[]:[]:[]"; end if;
        return strip(s);
    end if;
    if Detail gt 0 then printf "Constructing space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
    NS := NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1)));
    if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
    if NumberOfCoefficients eq 0 then
        if N le 1000 then NumberOfCoefficients := 1000; end if;
        if N gt 1000 and N le 4000 then NumberOfCoefficients := 2000; end if;
        if N gt 4000 and N le 10000 then NumberOfCoefficients := 3000; end if;
    end if;
    n := Max([SturmBound(N,k)+1,Floor(30*Sqrt(N)),NumberOfCoefficients]);
    assert QDimension(NS) eq dNS;
    if #TraceHint gt 0 then
        assert &and[t[1] ge 1:t in TraceHint] and &+[t[1]:t in TraceHint] eq dNS;
        assert #Set([#t:t in TraceHint]) eq 1;
        if #TraceHint eq 1 and DimensionsOnly then
            return strip(Sprintf("%o:%o:%o:%o:%o:", N, k, o, Cputime()-start, [TraceHint[1][1]]));
        end if;
        TraceHint := Sort(TraceHint);
        if #TraceHint[1] lt n then
            printf "*** Warning: ignoring TraceHint because it contains only %o < %o traces! ***", #TraceHint[1], n;
            TraceHint := [];
        end if;
        if #TraceHint eq 1 and DegreeBound gt 0 and dNS gt DegreeBound and EmbeddingPrecision eq 0 then
            if Detail gt 0 then printf "TraceHint implies that the space %o:%o:%o consists of a single orbit of dimension %o\n",N,k,o,dNS; end if;
            if Detail gt 0 and Order(chi) eq 1 then printf "Computing Atkin-Lehner signs for space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
            AL := Order(chi) eq 1 select [[<p,ExactQuotient(Trace(AtkinLehnerOperator(NS,p)),dNS)>:p in PrimeDivisors(N)]] else [];
            if Detail gt 0 and Order(chi) eq 1 then printf "took %o secs.\n", Cputime()-t; printf "Atkin-Lehner signs %o\n", sprint(AL); end if;
            if Detail gt 0 then printf "Checking whether single form in space %o:%o:%o has CM...", N,k,o; t:=Cputime(); end if;
            cm := [<proved select 1 else 0,st>] where st,proved:=SelfTwists([],NS:TraceHint:=TraceHint[1],pBound:=SelfTwistBound);
            if Detail gt 0 then printf "took %o secs.\n", Cputime()-t; printf "CM: %o\n", cm; end if;
            s := Sprintf("%o:%o:%o:%o:%o:%o:%o:[]:[[]]:[]:%o:[]:[]", N, k, o, Cputime()-start, [dNS], TraceHint, AL, cm);
            s cat:= Sprintf(":[]:[]:[]:[]:[%o]:[]",IsSelfDual(chi,dNS,TraceHint,[],NS) select 1 else 0);
            return strip(s);
        end if;
    end if;
    if Detail gt 0 then printf "Decomposing space %o:%o:%o of dimension %o...", N,k,o,dNS; t:=Cputime(); end if;
    S := NewformDecomposition(NS);
    if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
    D := [QDimension(S[i]): i in [1..#S]];
    if Detail gt 0 then printf "dims = %o\n", sprint(D); end if;
    if DimensionsOnly then
        return strip(Sprintf("%o:%o:%o:%o:%o:", N, k, o, Cputime()-start, Sort(D)));
    end if;
    if DegreeBound eq 0 then DegreeBound := Max(D); end if;
    if #TraceHint gt 0 then
        if Detail gt 0 then printf "Computing labels for forms in space %o:%o:%o using TraceHint...",N,k,o; t:=Cputime(); end if;
        assert Multiset([t[1]:t in TraceHint]) eq Multiset(D);
        // For forms with dimension in (1,DegreeBound], Compute trace bound sufficient to distinguish forms (if dimension is unique, this will be 1)
        M :=[1:d in D];
        for i := 1 to #M do
            if ComputeEigenvalues and D[i] gt 1 and D[i] le DegreeBound then
                M[i] := n;
            else
                m := n; for j:=1 to n do if #{t[1..j]:t in TraceHint|t[1] eq D[i]} eq #[t:t in TraceHint|t[1] eq D[i]] then m:=j; break; end if; end for;
                M[i] := m;
            end if;
        end for;
        F := [* M[i] gt 1 select Eigenform(S[i],M[i]+1) else 0 : i in [1..#S] *];
        T := []; DT := [t[1] : t in TraceHint];
        for i := 1 to #S do
            if M[i] eq 1 then
                ii := Index(DT,D[i]);
                T[i] := <[Integers()|TraceHint[ii][j] : j in [1..n]],i>;
            else
                T[i] := <[Integers()|Parent(a) eq Rationals() select a else AbsoluteTrace(a) where a:=Coefficient(F[i],j) : j in [1..n]],i>;
            end if;
        end for;
        T := Sort(T);
        if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
    else
        if Detail gt 0 then printf "Computing %o traces for space %o:%o:%o...", n, N,k,o; t:=Cputime(); end if;
        F := [*Eigenform(S[i],n+1):i in [1..#S]*];
        T := Sort([<[Integers()|Parent(a) eq Rationals() select a else AbsoluteTrace(a) where a:=Coefficient(F[i],j) : j in [1..n]],i> : i in [1..#F]]);
        if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
    end if;
    D := [D[T[i][2]] : i in [1..#T]];  S := [S[T[i][2]] : i in [1..#T]];  F := [*F[T[i][2]] : i in [1.. #T]*];
    T := [T[i][1] : i in [1..#T]];
    assert #Set(T) eq #T;
    if Detail gt 1 then printf "Lex sorted traces = %o\n", sprint(T); end if; 
    if Detail gt 0 and Order(chi) eq 1 then printf "Computing Atkin-Lehner signs for space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
    AL := Order(chi) eq 1 select [[<p,ExactQuotient(Trace(AtkinLehnerOperator(S[i],p)),D[i])>:p in PrimeDivisors(N)]:i in [1..#S]] else [];
    if Detail gt 0 and Order(chi) eq 1 then printf "took %o secs.\n", Cputime()-t; end if;
    if ComputeCutters and #[d:d in D|d le DegreeBound] gt 0 then
        HC:=[[]:d in D];   
        if #D gt 1 then
            if Detail gt 0 then printf "Computing Hecke cutters for space %o:%o:%o...",N,k,o; t:=Cputime(); end if;
            HC := ComputeHeckeCutters(S);
            if Detail gt 0 then printf "cutter length %o, took %o secs\n", #HC[1], Cputime()-t; end if;
        end if;
    else
        HC := [];
    end if;
    // Deal with 1-dimensional forms first
    HF := [[0,1]:d in D|d eq 1];  d1 := #HF;
    pra:=[1:i in [1..#HF]];
    u := UnitGenerators(chi);
    X := [<u,[Eltseq(v):v in ValuesOnUnitGenerators(chi)]>:i in [1..#HF]];
    cm := []; it := [];
    if ComputeTwists then
        for i:=1 to #HF do
            if Detail gt 0 then printf "Computing self twists for form %o:%o:%o:%o of dimension %o...",N,k,o,i,D[i]; t:=Cputime(); end if;
            cm[i] := <proved select 1 else 0,st> where st,proved := SelfTwists(T[i],S[i]:pBound:=SelfTwistBound);
            if Detail gt 0 then printf "found self twists %o in %o secs\n", cm[i], Cputime()-t; end if;
            if Detail gt 0 then printf "Computing inner twists for form %o:%o:%o:%o of dimension %o...",N,k,o,i,D[i]; t:=Cputime(); end if;
            it[i] := InnerTwistData(T[i],chi,k:CharTable:=CharTable);
            if Detail gt 0 then printf "found inner twists %o in %o secs\n", it[i], Cputime()-t; end if;
        end for;
    end if;
    // Now deal with forms of dimension 2 to DegreeBound
    E := [];
    if ComputeEigenvalues then
        R<x> := PolynomialRing(Rationals());
        for i:=d1+1 to #F do
            if D[i] gt DegreeBound then break; end if;
            if Detail gt 0 then printf "Computing %o exact Hecke eigenvalues form %o:%o:%o:%o of dimension %o...",n,N,k,o,i,D[i]; t:=Cputime(); end if;
            K := AbsoluteField(BaseRing(Parent(F[i])));
            f,b,a,c,d,pr,m := OptimizedOrderBasis(Eltseq(MinimalPolynomial(K.1)),[Eltseq(K!Coefficient(F[i],j)) : j in [1..n]]:Verbose:=Detail gt 0);
            aa := NFSeq(f,b,a);
            v := #u gt 0 select [Eltseq(z):z in EmbeddedCharacterValuesOnUnitGenerators(chi,k,aa)] else [];
            w := #u gt 0 select [Eltseq(r):r in Rows(Matrix(Rationals(),v)*Matrix(Rationals(),b)^-1)] else [];
            Append(~E,<f,b,c,<d,d eq 0 select Factorization(1) else Factorization(d)>,a,<u,w>,m>);  Append(~pra,pr select 1 else 0);  Append(~HF,f);  Append(~X,<u,v>);
            if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
            if ComputeTwists then 
                if Detail gt 0 then printf "Computing self twists for form %o:%o:%o:%o of dimension %o...",N,k,o,i,D[i]; t:=Cputime(); end if;
                cm[i] := <proved select 1 else 0,st> where st,proved := SelfTwists(aa,S[i]:pBound:=SelfTwistBound);
                if Detail gt 0 then printf "found self twists %o in %o secs\n", cm[i], Cputime()-t; end if;
                if Detail gt 0 then printf "Computing inner twists for form %o:%o:%o:%o of dimension %o...",N,k,o,i,D[i]; t:=Cputime(); end if;
                it[i] := InnerTwistData(aa,chi,k:CharTable:=CharTable);
                if Detail gt 0 then printf "found inner twists %o in %o secs\n", it[i], Cputime()-t; end if;
            end if;
        end for;
    else
        if ComputeTwists then
            for i:=d1+1 to #F do
                a := [Coefficient(F[i],j):j in [1..n]];
                if Detail gt 0 then printf "Computing self twists for form %o:%o:%o:%o of dimension %o...",N,k,o,i,D[i]; t:=Cputime(); end if;
                cm[i] := <proved select 1 else 0,st> where st,proved := SelfTwists(a,S[i]:pBound:=SelfTwistBound);
                if Detail gt 0 then printf "found self twists %o in %o secs\n", cm[i], Cputime()-t; end if;
                if Detail gt 0 then printf "Computing inner twists for form %o:%o:%o:%o of dimension %o...",N,k,o,i,D[i]; t:=Cputime(); end if;
                it[i] := InnerTwistData(a,chi,k:CharTable:=CharTable);
                if Detail gt 0 then printf "found inner twists %o in %o secs\n", it[i], Cputime()-t; end if;
            end for;
        end if;
    end if;
    if ComputeTwists then
        // Compute self twist data for remaining forms
        for i := #cm+1 to #F do
            if Detail gt 0 then printf "Computing self twists for form %o:%o:%o:%o of dimension %o...",N,k,o,i,D[i]; t:=Cputime(); end if;
            if F[i] ne 0 then
                a := [Coefficient(F[i],j):j in [1..n]];
                cm[i] := <proved select 1 else 0,st> where st,proved := SelfTwists(a,S[i]:pBound:=SelfTwistBound);
            else
                cm[i] := <proved select 1 else 0,st> where st,proved := SelfTwists([],S[i]:TraceHint:=TraceHint[i],pBound:=SelfTwistBound);
            end if;
            if Detail gt 0 then printf "found self twists %o in %o secs\n", cm[i], Cputime()-t; end if;
        end for;
    end if;
    if ComputeTraceStats then
        Z := []; M := []; H:=[];
        for i:=1 to #D do
            if D[i] gt DegreeBound then break; end if;
            if Detail gt 0 then printf "Computing trace stats for form %o:%o:%o:%o with dimension %o...",N,k,o,i,D[i]; t:=Cputime(); end if;
            z,m,h := TraceStats([Integers()!Trace(Trace(a)):a in SystemOfEigenvalues(S[i],8192)], k-1);
            z := Sprintf("%.3o",z lt 0.001 select 0 else z); m:=[Sprintf("%.3o",x lt 0.001 select 0 else x):x in m]; // trim precision (still ridiculous)
            Append(~Z,z); Append(~M,m); Append(~H,h);
            if Detail gt 0 then printf "took %o secs\n", Cputime()-t; printf "trace hash: %o\n", h; end if;
        end for;
    end if;
    eap := [];
    if EmbeddingPrecision gt 0 then
        P := PrimesInInterval(1,n);
        m := d1+#E;
        for i:=m+1 to #F do
            if Detail gt 0 then printf "Computing real/complex a_p for embeddings of form %o:%o:%o:%o of dimension %o...",N,k,o,i,D[i]; t:=Cputime(); end if;
            f := F[i];
            K := CoefficientRing(Parent(f)); dK := Degree(K); dB := Degree(BaseField(K));
            // list of lists of complex aps lex-ordered by [ii,jj] where ii indexes embeddings of Q(chi) and jj indexes relative embeddings of K
            if dB eq 1 then
                A := [[Conjugate(Coefficient(f,p),[jj]:Prec:=EmbeddingPrecision):p in P]:jj in [1..dK]];
            else
                A := [[Conjugate(Coefficient(f,p),[ii,jj]:Prec:=EmbeddingPrecision):p in P]:jj in [1..dK], ii in [1..dB]];
            end if;
            L := SortEmbeddings(f,chi,EmbeddingPrecision);
            // output embeddings in order (this implicitly labels them l.m where l is a Conrey index and m is an embedding index (lex order of a_n ordered by re,im)
            if o eq 1 then
                // for trivial character we just list real parts
                Append(~eap,[[Real(c):c in A[j]]:j in L]);
            else
                Append(~eap,[[[Real(c),Imaginary(c)]:c in A[j]]:j in L]);
            end if;
            // Sanity check that embedding data sums to traces for small p (we might not have enough precision for large p)
            CC := ComplexField(EmbeddingPrecision);
            assert [T[i][p]:p in P|p le 200] eq [Round(&+[CC!eap[#eap][j][jj]:j in [1..#eap[#eap]]]):jj in [1..#P]|P[jj] le 200];
            if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
        end for;
    end if;
    s := Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-start, D);
    s cat:= Sprintf(":%o:%o:%o:%o",T,AL,HF,HC);
    if ComputeEigenvalues then s cat:= Sprintf(":%o:%o:%o:%o",E,cm,it,pra); else s cat:= ":[]:[]:[]:[]"; end if;
    if ComputeTraceStats then s cat:= Sprintf(":%o:%o:%o", Z, M, H); else s cat:= ":[]:[]:[]"; end if;
    s cat:= Sprintf(":%o",X);
    if ComputeEigenvalues then s cat:= Sprintf(":%o",[IsSelfDual(chi,D[i],T[i],#HF ge i select HF[i] else [],S[i]) select 1 else 0:i in [1..#D]]); else s cat:= ":[]"; end if;
    s cat:= Sprintf(":%o",eap);
    if ReturnDecomposition then return strip(s),S; else return strip(s); end if;
end function;

procedure ValidateSpaceData (s:Coeffs:=1000,DegBound:=20,EmbeddingPrecision:=80,CharTable:=[])
    assert Coeffs gt 0;
    R<x>:=PolynomialRing(Integers());
    SetDefaultRealFieldPrecision(EmbeddingPrecision);
    r := Split(s,":");
    N := StringToInteger(r[1]); k := StringToInteger(r[2]); o := StringToInteger(r[3]);
    D := eval(r[5]); T := eval(r[6]); A := eval(r[7]); HF := eval(r[8]); HC := eval(r[9]); E := eval(r[10]); cm := eval(r[11]); twists := eval(r[12]); pra := eval(r[13]);
    zratio := eval(r[14]); zmoments := eval(r[15]); hash := eval(r[16]); X := eval(r[17]);  SD := eval(r[18]);
    if #r gt 18 then eap := eval(r[19]); else eap := []; end if;
    assert N gt 0 and k gt 0 and o gt 0;
    if o gt 1 then
        G := N le #CharTable select CharTable[N] else CharacterOrbitReps(N);
        assert o le #G;
        chi := G[o];    dchi := Degree(chi);
    else
        chi := DirichletGroup(N)!1;  dchi := 1;
    end if;
    // Check that D is a sorted list of integers whose sum is the dimension of the newspace (last condiction verified only for wt k>1) and that each d in D is divisible by the degree of Q(chi)
    assert Type(D) eq SeqEnum;
    if k gt 1 then assert sum(D) eq QDimensionNewCuspForms(chi,k); end if;
    if #D gt 0 then assert &and[Type(d) eq RngIntElt and d gt 0 and IsDivisibleBy(d,dchi):d in D]; end if;
    if DegBound eq 0 then DegBound := Max(D); end if;
    // Check that T is sorted list of lists of integers of equal length >= Coeffs with first entry matching dimension (absolute trace of 1)
    assert Type(T) eq SeqEnum;
    if #T gt 0 then assert Type(T[1]) eq SeqEnum and Type(T[1][1]) eq RngIntElt; end if;
    assert [t[1]:t in T] eq D;
    assert Sort(T) eq T;
    if #T gt 0 then assert #{#t:t in T} eq 1; assert #T[1] ge Coeffs; end if;
    // Check that A is an empty list unless character is trivial, in which case it should be a list of #D lists of pairs <p,sign>, one for each prime p|N 
    assert Type(A) eq SeqEnum;
    assert #A eq (o ne 1 select 0 else #D);
    if #A gt 0 then assert Type(A[1]) eq SeqEnum and {[p[1]:p in a]:a in A} eq {PrimeDivisors(N)} and &and[&and[p[2] in {-1,1}:p in a]:a in A]; end if;
    // Check that HF is a list of lists of integer coefficients of irreducible polys in Z[x] with degrees matching D for all d in D up to Degbound
    assert Type(HF) eq SeqEnum;
    assert #HF ge #[d:d in D|d le DegBound];
    if #HF gt 0 then assert Type(HF[1]) eq SeqEnum and &and[#HF[i] eq D[i]+1:i in [1..#HF]]; assert &and[Type(f) eq SeqEnum and Type(f[1]) eq RngIntElt and f[#f] eq 1 and IsIrreducible(R!f):f in HF]; end if;
    // Check that HC is a list of lists of tuples <p,[g0,g1,...]>, one for each entry in D, where each list of tuples projects to the same list of primes and g0,g1,...,1 encode irreducible monic polys
    // Also check that HC distiniughes ever form and that it is minimal in the sense that each additional entry increases the number of distinct lists, and that e
    assert Type(HC) eq SeqEnum;
    assert (k eq 1 and #HC eq 0) or (#HC eq #D and #Set(HC) eq #D) or (#[d:d in D|d le DegBound] eq 0 and #HC eq 0);
    if #D gt 0 and #HC eq 0 and #[d:d in D|d le DegBound] eq 0 then printf "Ignoring missing Hecke cutters in space %o:%o:%o with no forms below degree bound %o\n", N,k,o, DegBound; end if;
    if #HC gt 0 then
        assert Type(HC[1]) eq SeqEnum; assert #{[a[1]:a in c]:c in HC} eq 1; assert &and[IsPrime(c[1]):c in HC[1]];
        assert &and[&and[Type(a[2]) eq SeqEnum and Type(a[2][1]) eq RngIntElt and a[2][#a[2]] eq 1 and IsIrreducible(R!a[2]):a in c]:c in HC];
        assert #HC[1] lt #D; for n:= 2 to #HC[1] do assert #{c[1..n]:c in HC} gt #{c[1..n-1]:c in HC}; end for;
    end if;
    // Check that E is a list of 5-tuples <g,b,n,m,a> encoding Hecke eigenvalue data for each entry d in D with 1 < d <= DegBound where
    // g is a list of integers encoding an irreducible monic poly of degree d, 
    // b is a list of lists of rationals encoding a basis for the Hecke ring in terms of the power basis defined by g
    // n is a positive integer (a divisor of the index of the Hecke ring in the maximal order, not checked)
    // m is 0 or 1 (indicates whether or not n is equal to the index)
    // a is a list of lists of d integers encoding eigenvalues a_1,a_2,... in terms of the basis b
    assert Type(E) eq SeqEnum and #E ge #[d:d in D|1 lt d and d le DegBound];
    off := #[d:d in D|d eq 1];
    for i:= 1 to  #E do
        e := E[i]; d := D[off+i];
        assert Type(e) eq Tup and #e ge 5;
        assert Type(e[1]) eq SeqEnum and e[1] eq HF[off+i];
        assert Type(e[2]) eq SeqEnum and #e[2] eq d and {#a:a in e[2]} eq {d} and Determinant(Matrix(Rationals(),e[2])) ne 0;
        assert Type(e[3]) eq RngIntElt and e[3] gt 0;
        assert e[4] eq <0,[]> or Abs(e[4][1]) eq prod([q[1]^q[2]:q in e[4][2]]);
        assert Type(e[5]) eq SeqEnum and Type(e[5][1]) eq SeqEnum and Type(e[5][1][1]) eq RngIntElt;
        assert #e[5] ge Coeffs and #e[5] le #T[off+i] and {#c:c in e[5]} eq {d};
        // Verify that traces match
        a := NFSeq(e[1],e[2],e[5]);
        assert [Trace(c):c in a] eq [T[off+i][n]:n in [1..#e[5]]];
        // Check character values if present
        assert n eq o where _,n := CharacterFromValues(N,e[6][1],NFSeq(e[1],e[2],e[6][2]):Orbit);
        assert CheckOrderGeneratorBound (e[1], [Eltseq(r) : r in Rows(Matrix(Rationals(),e[5])*Matrix(Rationals(),e[2]))], e[7]) eq 0;
    end for;
    // Check that cm is a list of pairs <b,st> where b is 0 or 1 and st is a list of fundamental discriminants
    assert Type(cm) eq SeqEnum and #cm ge #[d:d in D|d le DegBound];
    if #cm gt 0 then assert &and[x[1] in [0,1] and Type(x[2]) eq SeqEnum and #x[2] in [0,1,3] and (#x[2] eq 0 or &and[IsDiscriminant(d):d in x[2]]) : x in cm]; end if;
    // Check that twists is a list of lists of quadruples, one for each d in D up to DegBound, where each quadruple <b,n,m,o> has b in [0,1], n pos int, m a modulus supported on primes dividing N, and o a character orbit of modulus m
    assert Type(twists) eq SeqEnum and #twists eq #HF;
    if #twists gt 0 then
        P := Set(PrimeDivisors(N));
        for tw in twists do
            assert Type(tw) eq SeqEnum;
            for t in tw do
                assert #t eq 4 and t[1] in [0,1] and Type(t[2]) eq RngIntElt and t[2] ge 1 and Set(PrimeDivisors(t[3])) subset P and Type(t[4]) eq RngIntElt and t[4] ge 2 and t[4] le NumberOfCharacterOrbits(t[3]);
            end for;
        end for;
    end if;
    // Check that pra is a list of integers in [0,1], one for each polynomial in HF
    assert Type(pra) eq SeqEnum and #pra eq #HF and Set(pra) subset {0,1};
    // If non-empty, check that zratios is a list of real numbers in [0,1]
    assert Type(zratio) eq SeqEnum;
    if #zratio gt 0 then assert #zratio le #D and &and[r ge 0.0 and r lt 1.0:r in zratio]; end if;
    // If non-empty check that zmoments is a list of lists of real numbers (moments of normalized traces)
    assert Type(zmoments) eq SeqEnum;
    if #zmoments gt 0 then assert #zmoments le #D and &and[Type(m) eq SeqEnum and Type(m[1]) eq FldReElt:m in zmoments]; end if;
    // For k > 1 check that hash is a list of integers in [0,2^61-1], one for each d in D up to DegBound
    assert Type(hash) eq SeqEnum and ((k eq 1 and #hash eq 0) or #hash ge #[d:d in D|d le DegBound]);
    if #hash gt 0 then assert &and[Type(h) eq RngIntElt and h ge 0 and h lt 2^61-1:h in hash]; end if;
    // Check that X is a list of pairs <u,v> defining character chi with values in K=Q[x]/(f(x)) for each f in HF
    assert Type(X) eq SeqEnum and #X eq #HF;
    for i:= 1 to #X do assert n eq o where _,n := CharacterFromValues (N,X[i][1],[K|x:x in X[i][2]]:Orbit) where K:=NumberField(R!HF[i]); end for;
    // Verify that SD is a list of integer in [0,1], one for each entry in D, and check that odd dimensional spaces are marked as self-dual.
    assert #SD eq #D and &and[b in [0,1] : b in SD] and &and[SD[i] eq 1:i in [1..#D]|IsOdd(D[i])];
    XD := [d:d in D|d gt DegBound];
    if #r ge 19 then
        // verify that eap is a list of lists of complex embedded ap values, one for each subspace of dimension greater than DegBound
        m := #D-#XD;
        assert #eap eq #XD;
        if #eap gt 0 then
            P := PrimesInInterval(1,#T[1]);
            for i := 1 to #eap do
                assert #eap[i] eq XD[i] and &and[#a eq #P : a in eap[i]];
                for j := 1 to #P do 
                    if T[m+i][P[j]] eq 0 then
                        assert Abs(&+[a[j] : a in eap[i]]) lt 10^-20;
                    else
                        assert Abs(&+[a[j] : a in eap[i]] / T[m+i][P[j]] - 1.0) lt 10^-20;
                    end if;
                end for;
            end for;
        end if;
    else
        if #XD gt 0 then printf "Warning: no embedded ap values in space %o:%o:%o containing %o forms of dimension greater than degree bound %o\n", N,k,o,#XD,DegBound; end if;
    end if;
end procedure;

procedure ValidateDataFile (infile:Coeffs:=1000,DegBound:=20,EmbeddingPrecision:=80,Quiet:=false,Jobs:=1,JobId:=0,SplitInput:=false)
    start := Cputime();
    if SplitInput and Jobs ne 1 then infile cat:= Sprintf("_%o",JobId); end if;
    S:=Split(Read(infile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S, infile; end if;
    n := 0;
    for i:=1 to #S do
        s := S[i];
        n +:= 1;
        if SplitInput or ((n-JobId) mod Jobs) eq 0 then
            if not Quiet then t := Cputime(); end if;
            ValidateSpaceData(s:Coeffs:=Coeffs,DegBound:=DegBound,EmbeddingPrecision:=EmbeddingPrecision);
            if not Quiet then printf "Validated data for space %o:%o:%o:%o in record %o in %o secs\n", r[1],r[2],r[3],r[5],i,Cputime()-t where r:=Split(s,":"); end if;
        end if;
    end for;
    printf "Validated %o data records in %o secs\n", n, Cputime()-start;
end procedure;

// given strings s1 and s2 containing data for a new space (tuples of length at least 5 and at most 18), returns the index of the first entry where they disagree, or zero if they are isomorphic
function CompareSpaceData (s1,s2:DoNotCheck:=[])
    assert Set(DoNotCheck) subset Set([4] cat [6..19]);
    r1 := Split(strip(s1),":");
    r2 := Split(strip(s2),":");
    assert #r1 ge 5 and #r2 ge 5 and #r1 le 19 and #r2 le 19;
    if r1[1] ne r2[1] then return 1; end if;
    if r1[2] ne r2[2] then return 2; end if;
    if r1[3] ne r2[3] then return 3; end if;
    if r1[5] ne r2[5] then return 5; end if;
    mm := Min(#r1,#r2);
    n := 5;
    while n lt mm do
        n +:= 1;
        if n in DoNotCheck then continue; end if;
        if r1[n] eq r2[n] then continue; end if;
        if n in {6,7,9,14,15,16,18,19} then
            if r1[n] ne r2[n] then return n; end if;
        end if;
        if n eq 8 then
            HF1 := eval(r1[n]); HF2 := eval(r2[n]);
            if #HF1 ne #HF2 then return n; end if;
            for i:=1 to #HF1 do if not NFPolyIsIsomorphic(HF1[i],HF2[i]) then return n; end if; end for;
        end if;
        if n eq 10 then
            E1 := eval(r1[n]); E2 := eval(r2[n]);
            if #E1 ne #E2 then return n; end if;
            for i:=1 to #E1 do
                e1 := E1[i];  e2 := E2[i];
                if e1 eq e2 then continue; end if;
                if e1[4][1] ne 0 or e2[4][1] ne 0 then
                    if e1[3] ne e2[3] or e1[4] ne e2[4] then return n; end if;
                end if;
                if not NFPolyIsIsomorphic(E1[i][1],E2[i][1]) then return n; end if;
                C1 := [Eltseq(r) : r in Rows(Matrix(Rationals(),e1[5])*Matrix(Rationals(),e1[2]))];
                C2 := [Eltseq(r) : r in Rows(Matrix(Rationals(),e2[5])*Matrix(Rationals(),e2[2]))];
                if #C1 ne #C2 then printf "%o:%o:%o: warning, different number %o != %o of eigenvalues in entry %o of eigenvalue data\n", r1[1],r1[2],r1[3], #C1, #C2, i; end if;
                m := Min(#C1,#C2); C1 := [C1[j]:j in [1..m]]; C2 := [C2[j]:j in [1..m]];
                if #e1 ge 6 and #e2 ge 6 then
                    if e1[6][1] ne e2[6][1] then return n; end if;
                    if #e1[6][2] ne #e2[6][2] then return n; end if;
                    if #e1[6][2] gt 0 then
                        C1 cat:= [Eltseq(r) : r in Rows(Matrix(Rationals(),e1[6][2])*Matrix(Rationals(),e1[2]))];
                        C2 cat:= [Eltseq(r) : r in Rows(Matrix(Rationals(),e2[6][2])*Matrix(Rationals(),e2[2]))];
                    end if;
                end if;
                if e1[1] ne e2[1] or C1 ne C2 then
                    if not NFSeqIsIsomorphic(E1[i][1],C1,E2[i][1],C2) then printf "%o:%o:%o: error, eigenvalue mismatch for entry %o of eigenvalue data\n", r1[1],r1[2],r1[3],i; return n; end if;
                end if;
                if #e1 ge 7 and #e2 ge 7 then
                    if e1[7] ne e2[7] then printf "%o:%o:%o: error, coefficient ring generator nbound mismatch for entry %o of eigenvalue data\n", r1[1], r1[2], r1[3], i; return n; end if;
                end if;
            end for;
        end if;
        if n eq 11 then
            cm1 := eval(r1[n]); cm2 := eval(r2[n]);
            if #cm1 ne #cm2 or not &and[Set(cm1[i][2]) eq Set(cm2[i][2]): i in [1..#cm1]] then return n; end if;
        end if;
        if n eq 12 then
            tw1 := eval(r1[n]); tw2 := eval(r2[n]);
            if not #tw1 eq #tw2 or not &and[Set([tw1[i][j]:j in [2..4]]) eq Set([tw2[i][j]:j in [2..4]]): i in [1..#tw1]] then return n; end if;
        end if;
        if n eq 13 then
            pra1 := eval(r1[n]);  pra2 := eval(r2[n]);
            if #pra1 ne #pra2 then return n; end if;
        end if;
        if n eq 17 then
            HF1 := eval(r1[8]); HF2 := eval(r2[8]);
            x1 := eval(r1[n]);  x2 := eval(r2[n]);
            if #x1 ne #x2 or not &and[x1[i][1] eq x2[i][1]:i in [1..#r1[n]]] or not &and[NFSeqIsIsomorphic(HF1[i],x1[i][2],HF2[i],x2[i][2]):i in [1..#x1]] then return n; end if;
        end if;
        if n eq 18 and #r1 ge 18 and #r2 ge 18 then
            if r1[18] ne r2[18] then return n; end if;
        end if;
        if n eq 19 and #r1 ge 19 and #r2 ge 19 then
            if r1[19] ne r2[19] then return n; end if;
        end if;
    end while;
    return #r1 eq #r2 select 0 else mm+1;
end function;


function CompareDataFiles (infile1,infile2:DoNotCheck:=[],Quiet:=false,Jobs:=1,JobId:=0)
    start := Cputime();
    S1 := Split(Read(infile1),"\n");
    S2 := Split(Read(infile2),"\n");
    if not Quiet then printf "Loaded %o records from file %o and %o records from file %o in %o secs\n", #S1, infile1, #S2, infile2, Cputime()-start; end if;
    if #S1 ne #S2 then printf "Files %o and %o do not have the same number of records: %o vs %o\n", infile1, infile2, #S1, #S2; return false; end if;
    start := Cputime();
    cnt := 0;
    for i:=1 to #S1 do
        if ((i-JobId) mod Jobs) eq 0 then
            cnt +:= 1;
            if S1[i] eq S2[i] then continue; end if;
            if not Quiet then printf "Checking records at line %o...", i; t := Cputime(); end if;
            j := CompareSpaceData (S1[i],S2[i]:DoNotCheck:=DoNotCheck);
            if j gt 0 then printf "Error, mismatch at column %o for records at line %o\n", j, i; return false; end if;
            if not Quiet then printf "success in %o secs\n", Cputime()-t; end if;
        end if;
    end for;
    printf "Succesfully matched %o of %o lines from files %o and %o in %o secs\n", cnt, #S1, infile1, infile2, Cputime()-start;
    return true;
end function;

// Decompose spaces S_k(N,chi)^new into Galois stable subspaces for B0 < k^2*N <= B and k > 1.
procedure DecomposeSpaces (outfile,B:TodoFile:="",B0:=0,Quiet:=false,DimensionsOnly:=false,Coeffs:=1000,DegBound:=20,TrivialCharOnly:=false,TraceStats:=false,Precision:=0,Jobs:=1,JobId:=0)
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    if TodoFile ne "" then
        TodoList := AssociativeArray();
        for s in Split(Read(TodoFile),"\n") do
            r := Split(s,":");
            TodoList[[StringToInteger(r[1]),StringToInteger(r[2]),StringToInteger(r[3])]] := #r ge 5 select eval(r[5]) else [];
        end for;
        L := {r[1]:r in Keys(TodoList)};
        printf "Loaded todo list with %o items from %o\n", #Keys(TodoList), TodoFile;
    else
        L := {};
    end if;
    st := Cputime();
    n := 0; cnt:=0;
    fp := Open(outfile,"w");
    A := AssociativeArray();
    for N:=1 to Floor(B/4) do
        if #L gt 0 and not N in L then continue; end if;
        if not TrivialCharOnly then
            if not Quiet then printf "Constructing character orbit table for modulus %o...", N; t:=Cputime(); end if;
            G, T := CharacterOrbitReps(N:RepTable); A[N] := <G,T>;
            if not Quiet then printf "took %o secs\n",Cputime()-t; end if;
        end if;
        for k := Max(2,Floor(Sqrt(B0/N))+1) to Floor(Sqrt(B/N)) do
            m := TrivialCharOnly select 1 else #A[N][1];
            for o in [1..m] do
                if #L gt 0 and not IsDefined(TodoList,[N,k,o]) then continue; end if;
                hint := #L gt 0 select TodoList[[N,k,o]] else [];
                chi := o gt 1 select A[N][1][o] else DirichletGroup(N)!1;
                n +:= 1;
                if ((n-JobId) mod Jobs) eq 0 then
                    if DimensionsOnly then
                        str := NewspaceData(chi,k,o:DimensionsOnly:=true,Detail:=Quiet select 0 else 1);
                    else
                        // Note that we need character orbit tables even when TrivialCharOnly is set because we may have twists by non-trivial characters (e.g. for CM forms)
                        if not Quiet then printf "Constructing character orbit table for divisors of modulus %o...", N; t:=Cputime(); end if;
                        for M in Divisors(N) do if not IsDefined(A,M) then G, T := CharacterOrbitReps(M:RepTable); A[M] := <G,T>; end if; end for;
                        if not Quiet then printf "took %o secs\n",Cputime()-t; end if;
                        if not Quiet then printf "\nProcessing space %o:%o:%o with Coeffs=%o, DegBound=%o\n", N,k,o, Coeffs, DegBound; t:=Cputime(); end if;
                        str := NewspaceData(chi,k,o:CharTable:=A,TraceHint:=hint,NumberOfCoefficients:=Coeffs,ComputeEigenvalues,ComputeCutters,EmbeddingPrecision:=Precision,ComputeTwists,ComputeTraceStats:=TraceStats,DegreeBound:=DegBound,Detail:=Quiet select 0 else 1);
                        if not Quiet then printf "Total time for space %o:%o:%o was %os\n\n", N,k,o,Cputime()-t; end if;
                    end if;
                    Puts(fp,str);
                    Flush(fp);
                    cnt +:= 1;
                end if;
            end for;
        end for;
    end for;
    printf "Wrote %o records to %o using %os of CPU time.\n", cnt, outfile, Cputime()-st;
end procedure;


// Decompose spaces S_k(N,chi)^new into Galois stable subspaces for B0 < k^2*N <= B and k > 1.
procedure DecomposeSpace (outfile,B:TodoFile:="",B0:=0,Quiet:=false,DimensionsOnly:=false,Coeffs:=1000,DegBound:=20,TrivialCharOnly:=false,TraceStats:=false,Precision:=0,Jobs:=1,JobId:=0)
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    if TodoFile ne "" then
        TodoList := AssociativeArray();
        for s in Split(Read(TodoFile),"\n") do
            r := Split(s,":");
            TodoList[[StringToInteger(r[1]),StringToInteger(r[2]),StringToInteger(r[3])]] := #r ge 5 select eval(r[5]) else [];
        end for;
        L := {r[1]:r in Keys(TodoList)};
        printf "Loaded todo list with %o items from %o\n", #Keys(TodoList), TodoFile;
    else
        L := {};
    end if;
    st := Cputime();
    n := 0; cnt:=0;
    fp := Open(outfile,"w");
    A := AssociativeArray();
    for N:=1 to Floor(B/4) do
        if #L gt 0 and not N in L then continue; end if;
        if not TrivialCharOnly then
            if not Quiet then printf "Constructing character orbit table for modulus %o...", N; t:=Cputime(); end if;
            G, T := CharacterOrbitReps(N:RepTable); A[N] := <G,T>;
            if not Quiet then printf "took %o secs\n",Cputime()-t; end if;
        end if;
        for k := Max(2,Floor(Sqrt(B0/N))+1) to Floor(Sqrt(B/N)) do
            m := TrivialCharOnly select 1 else #A[N][1];
            for o in [1..m] do
                if #L gt 0 and not IsDefined(TodoList,[N,k,o]) then continue; end if;
                hint := #L gt 0 select TodoList[[N,k,o]] else [];
                chi := o gt 1 select A[N][1][o] else DirichletGroup(N)!1;
                n +:= 1;
                if ((n-JobId) mod Jobs) eq 0 then
                    if DimensionsOnly then
                        str := NewspaceData(chi,k,o:DimensionsOnly:=true,Detail:=Quiet select 0 else 1);
                    else
                        // Note that we need character orbit tables even when TrivialCharOnly is set because we may have twists by non-trivial characters (e.g. for CM forms)
                        if not Quiet then printf "Constructing character orbit table for divisors of modulus %o...", N; t:=Cputime(); end if;
                        for M in Divisors(N) do if not IsDefined(A,M) then G, T := CharacterOrbitReps(M:RepTable); A[M] := <G,T>; end if; end for;
                        if not Quiet then printf "took %o secs\n",Cputime()-t; end if;
                        if not Quiet then printf "\nProcessing space %o:%o:%o with Coeffs=%o, DegBound=%o\n", N,k,o, Coeffs, DegBound; t:=Cputime(); end if;
                        str := NewspaceData(chi,k,o:CharTable:=A,TraceHint:=hint,NumberOfCoefficients:=Coeffs,ComputeEigenvalues,ComputeCutters,EmbeddingPrecision:=Precision,ComputeTwists,ComputeTraceStats:=TraceStats,DegreeBound:=DegBound,Detail:=Quiet select 0 else 1);
                        if not Quiet then printf "Total time for space %o:%o:%o was %os\n\n", N,k,o,Cputime()-t; end if;
                    end if;
                    Puts(fp,str);
                    Flush(fp);
                    cnt +:= 1;
                end if;
            end for;
        end for;
    end for;
    printf "Wrote %o records to %o using %os of CPU time.\n", cnt, outfile, Cputime()-st;
end procedure;

procedure OptimizeCoefficients (infile,outfile:Quiet:=false,Jobs:=1,JobId:=0,SplitInput:=false)
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    if SplitInput then infile cat:= Sprintf("_%o",JobId); end if;
    S:=Split(Read(infile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S, infile; end if;
    fp := Open(outfile,"w");
    n := 0; cnt := 0;
    T := AssociativeArray(Integers());
    for s in S do
        n +:= 1;
        if not SplitInput and ((n-JobId) mod Jobs) ne 0 then continue; end if;
        t := Cputime();
        r := Split(s,":");
        N := StringToInteger(r[1]);
        k := StringToInteger(r[2]);
        o := StringToInteger(r[3]);
        D := eval(r[5]);
        HF := eval(r[8]);
        inE := eval(r[10]);
        pra := eval(r[13]);
        d1 := #[d:d in D|d eq 1];
        if #inE gt 0 then
            if not IsDefined(T,N) then T[N] := CharacterOrbitReps(N); end if;
            chi := T[N][o];
            u := UnitGenerators(chi);
        end if;
        E := [];
        for i:=1 to #inE do
            e := inE[i];
            assert e[1] eq HF[d1+i];
            aa := [Eltseq(a):a in Rows(Matrix(Rationals(),e[5])*Matrix(Rationals(),e[2]))];
            f,b,a,c,d,pr,m := OptimizedOrderBasis([Rationals()!a:a in e[1]],aa:KBestPoly:=e[1],KBestIsPolredabs:=pra[d1+i] eq 1 select true else false,Verbose);
            v := #u gt 0 select [Eltseq(z):z in EmbeddedCharacterValuesOnUnitGenerators(chi,k,NFSeq(f,b,a))] else [];
            w := #u gt 0 select [Eltseq(r):r in Rows(Matrix(Rationals(),v)*Matrix(Rationals(),b)^-1)] else [];
            E[i] := <f,b,c,<d,d eq 0 select Factorization(1) else Factorization(d)>,a,<u,w>,m>;
            ee := E[i];
            assert e[1] eq ee[1];
            bb := [Eltseq(b):b in Rows(Matrix(Rationals(),ee[5])*Matrix(Rationals(),ee[2]))];
            assert aa eq bb;
            assert #sprint(ee) le 1.05*(#sprint(e)+100);
        end for;
        if #E gt 0 then r[10] := sprint(E); end if;
        Puts(fp,Join(r,":"));
        Flush(fp);
        cnt +:= 1;
        if not Quiet and #E gt 0 then printf "%o:%o:%o:%o (%.3os)\n",r[1],r[2],r[3],r[5],Cputime()-t; end if;
    end for;
    if not Quiet then printf "Wrote %o of %o records to %o\n", cnt, #S, outfile; end if;
end procedure;

procedure ProcessPariGPData (infile,outfile:Quiet:=false,Jobs:=1,JobId:=0)
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    S:=Split(Read(infile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S, infile; end if;
    fp := Open(outfile,"w");
    n := 0; cnt := 0;
    T := AssociativeArray(Integers());
    for s in S do
        n +:= 1;
        if ((n-JobId) mod Jobs) eq 0 then
            t := Cputime();
            r := Split(s,":");
            N := StringToInteger(r[1]);
            k := StringToInteger(r[2]);
            o := StringToInteger(r[3]);
            D := eval(r[5]);
            inE := eval(r[10]);
            inHF := eval(r[8]);
            HF:=[[0,1]:i in [1..#D]|D[i] eq 1];  E:=[];  pra:=[1:i in [1..#HF]];
            if #D gt 0 then
                if not IsDefined(T,N) then T[N] := CharacterOrbitReps(N); end if;
                chi := T[N][o];
                u := UnitGenerators(chi);
            end if;
            X := [<u,[Eltseq(v):v in ValuesOnUnitGenerators(chi)]>:d in D|d eq 1];
            for e in inE do
                aa := [Eltseq(a):a in Rows(Matrix(Rationals(),e[5])*Matrix(Rationals(),e[2]))];
                f,b,a,c,d,pr := OptimizedOrderBasis([Rationals()!a:a in e[1]],aa);
                v := #u gt 0 select [Eltseq(z):z in EmbeddedCharacterValuesOnUnitGenerators(chi,k,NFSeq(f,b,a))] else [];
                w := #u gt 0 select [Eltseq(r):r in Rows(Matrix(Rationals(),v)*Matrix(Rationals(),b)^-1)] else [];
                Append(~E,<f,b,c,d eq 0 select 0 else 1,a,<u,w>>);  Append(~pra,pr select 1 else 0);  Append(~HF,f); Append(~X,<u,v>);
            end for;
            assert #E eq #inE;
            assert #pra eq #HF;
            assert #X eq #HF;
            Puts(fp,strip(Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:[]:[]:[]:%o",r[1],r[2],r[3],r[4],r[5],r[6],r[7],HF,r[9],E,r[11],r[12],pra,X)));
            Flush(fp);
            cnt +:= 1;
            if not Quiet and #D gt 0 then printf "%o:%o:%o:%o (%.3os)\n",r[1],r[2],r[3],r[5],Cputime()-t; end if;
        end if;
    end for;
    if not Quiet then printf "Wrote %o of %o records to %o\n", cnt, #S, outfile; end if;
end procedure;

procedure NFPolyUpdate (infile,outfile,nfpolyfile)
    R := PolynomialRing(Rationals());
    S := [Split(r,":"):r in Split(Read(nfpolyfile),"\n")];
    A := AssociativeArray();
    for s in S do
        if s[2] eq "[]" then continue; end if; // if we don't know the polredabs poly ignore it
        f := StringToIntegerArray(s[1]); g := StringToIntegerArray(s[2]); d := StringToInteger(s[3]); a := eval(s[4]);
        assert d ne 0 and #a ne 0;             // if we have the polredabs poly we should have the number field disc and its factorization
        A[f] := <g,d,a>;
    end for;
    printf "Loaded %o records from nfpolyfile %o\n", #Keys(A), nfpolyfile;
    start := Cputime();
    S := Split(Read(infile),"\n");
    printf "Loaded %o data records from %o in %o secs\n", #S, infile, Cputime()-start;
    T := AssociativeArray();
    start := Cputime();
    fp := Open(outfile,"w");
    cnt := 0; ccnt := 0;
    for s in S do
        r := Split(s,":");
        if r[8] eq "[]" then cnt +:= 1; Puts(fp,s); continue; end if;
        pra := eval(r[13]);
        if not 0 in pra then cnt +:= 1; Puts(fp,s); continue; end if;
        N := StringToInteger(r[1]);
        k := StringToInteger(r[2]);
        o := StringToInteger(r[3]);
        D := eval(r[5]);
        F := eval(r[8]);
        E := eval(r[10]);
        X := eval(r[17]);
        if N gt 2 then for i:=1 to #F do assert {#x+1:x in X[i][2]} eq {#F[i]}; end for; end if;
        off := #[d:d in D|d eq 1];
        update := false;
        // the code below is an annoying hack to avoid magma complaints about type mismatches when changing empty lists to non-empty lists in tuples
        if #E gt 0 then
            Eout :=[<[1,0],[[Rationals()|1]],1,<1,[<1,1>]>,[[1]],<[1],[[1]]>,1>]; // stub to get correct universe
            for i:=1 to #E do Eout[i] := E[i]; end for;
            E := Eout;
        end if;
        if #X gt 0 then
            Xout :=[<[1],[[Rationals()|1]]>]; // stub to get correct universe
            for i:=1 to #X do Xout[i] := X[i]; end for;
            X := Xout;
        end if;
        for i in [1..#pra] do
            if pra[i] eq 0 then
                assert i ge off;
                if IsDefined(A,F[i]) then
                    newf := A[F[i]][1]; newd := A[F[i]][2]; newfac := A[F[i]][3];
                    e := E[i-off];
                    assert e[1] eq F[i];
                    assert #e ge 7 and #e[4] eq 2;
                    if e[4][1] ne 0 then
                        assert e[4][1] eq newd and e[4][2] eq newfac;
                        if newf eq F[i] then
                            printf "Setting polredabs flag for %o:%o:%o:%o...\n", r[1],r[2],r[3],i;
                            pra[i]:=1;
                            update := true;
                            continue;
                        end if;
                    end if;
                    printf "Updating data for %o:%o:%o:%o...poly %o changing\n", r[1],r[2],r[3],i,e[1] eq newf select "is not" else "is";  t:=Cputime();
                    if e[1] ne newf then printf "%o\n%o\n",sprint(e[1]),sprint(newf); end if;
                    if not IsDefined(T,N) then T[N] := CharacterOrbitReps(N); end if;
                    chi := T[N][o];
                    u := UnitGenerators(chi);
                    aa := [Eltseq(a):a in Rows(Matrix(Rationals(),e[5])*Matrix(Rationals(),e[2]))];
                    f,b,a,c,d,pr,m := OptimizedOrderBasis([Rationals()!x:x in e[1]],aa:KBestPoly:=newf,KBestIsPolredabs:=true,KDisc:=newd);
                    v := #u gt 0 select [Eltseq(z):z in EmbeddedCharacterValuesOnUnitGenerators(chi,k,NFSeq(f,b,a))] else [];
                    w := #u gt 0 select [Eltseq(r):r in Rows(Matrix(Rationals(),v)*Matrix(Rationals(),b)^-1)] else [];
                    assert f eq newf and d eq newd and pr;
                    assert NFSeqIsIsomorphic(NFSeq(e[1],e[2],e[5]),NFSeq(f,b,a));
                    assert n eq o where _,n := CharacterFromValues(N,u,NFSeq(f,b,w):Orbit);
                    assert n eq o where _,n := CharacterFromValues (N,u,[K|x:x in v]:Orbit) where K:=NumberField(R!f);
                    if e[4][1] ne 0 then assert m eq e[7]; else assert IsDivisibleBy(m,e[7]); end if;
                    if e[4][1] eq 0 then if m eq e[7] then printf "Index %o is now proved!\n", m; else printf "*** Corrected index form %o to %o ***\n", e[7],m; end if; end if;
                    F[i] := f;
                    E[i-off] := <f,b,c,<newd,newfac>,a,<u,w>,m>;
                    X[i] := <u,v>;
                    pra[i] := 1;
                    printf "Update took %o secs\n", Cputime()-t;
                    update := true;
                end if;
            end if;
        end for;
        cnt +:= 1;
        if update then
            r[8] := sprint(F);
            r[10] := sprint(E);
            r[13] := sprint(pra);
            r[17] := sprint(X);
            Puts(fp,Join(r,":"));
            ccnt +:= 1;
        else
            Puts(fp,s);
        end if;
    end for;
    printf "Wrote %o records to %o in %o secs, changed %o records\n", cnt, outfile, Cputime()-start, ccnt;
end procedure;


procedure DiagonalizePermutationBases (infile,outfile:Quiet:=false,Jobs:=1,JobId:=0,SplitInput:=false)
    start := Cputime();
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    if SplitInput and Jobs ne 1 then infile cat:= Sprintf("_%o",JobId); end if;
    S:=Split(Read(infile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S, infile; end if;
    fp := Open(outfile,"w");
    n := 0; cnt := 0; ccnt := 0;
    for s in S do
        n +:= 1;
        if SplitInput or ((n-JobId) mod Jobs) eq 0 then
            r := Split(s,":");
            if r[10] eq "[]" then Puts(fp,s); cnt +:=1; continue; end if;
            E := eval(r[10]);
            I := [i : i in [1..#E] | IsPermutationMatrix(e[2]) and not IsDiagonalMatrix(e[2]) where e:=E[i]];
            if #I eq 0 then  Puts(fp,s); cnt +:=1; continue; end if;
            for i in I do
                e := E[i];
                m := #e[2];
                if not Quiet then printf "Diagonalizing permutation basis for form of dimension %o in space %o:%o:%o\n", m,r[1],r[2],r[3]; t := Cputime(); end if;
                a := NFSeq(e[1],e[2],e[5]);
                P := Matrix(Rationals(),[[e[2][j][i] eq 0 select 0 else 1:j in [1..m]]:i in [1..m]]);
                B := P*Matrix(Rationals(),e[2]);  assert IsDiagonal(B); B := [Eltseq(x):x in Rows(B)];
                c := Matrix(Rationals(),e[5])*P^-1; c := [Eltseq(x):x in Rows(c)];
                v := Matrix(Rationals(),e[6][2])*P^-1; v := [Eltseq(x):x in Rows(v)];
                assert NFSeqIsIsomorphic(NFSeq(e[1],e[2],e[5] cat e[6][2]),NFSeq(e[1],B,c cat v));
                e := <e[1],B,e[3],e[4],c,<e[6][1],v>,e[7]>;
                E[i] := e;
                if not Quiet then printf "Diagonlization and verification took %o.3s\n", Cputime()-t; end if;
            end for;
            r[10] := sprint(E);
            Puts(fp,Join(r,":"));
            ccnt +:= 1;
            cnt +:= 1;
        end if;
    end for;
    Flush(fp);
    printf "Wrote %o records to %o in %o secs, changed %o records\n", cnt, outfile, Cputime()-start, ccnt;
end procedure;

        
procedure AddCharacterValues (infile,outfile:Quiet:=false,Jobs:=1,JobId:=0)
    start := Cputime();
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    S:=Split(Read(infile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S, infile; end if;
    fp := Open(outfile,"w");
    n := 0; cnt := 0;
    T := AssociativeArray();
    for s in S do
        n +:= 1;
        if ((n-JobId) mod Jobs) eq 0 then
            t := Cputime();
            r := Split(s,":");
            assert #r le 17;
            if #r eq 17 then Puts(fp,s); continue; end if;
            if r[5] eq "[]" then Puts(fp,s cat ":[]"); continue; end if;
            N := StringToInteger(r[1]);
            if not IsDefined(T,N) then T[N] := CharacterOrbitReps(N); end if;
            k := StringToInteger(r[2]);
            o := StringToInteger(r[3]);
            chi := T[N][o];
            u := UnitGenerators(chi);
            D := eval(r[5]);
            F := eval(r[8]);
            E := eval(r[10]);
            X := [<u,[Eltseq(z):z in ValuesOnUnitGenerators(chi)]>:d in D|d eq 1];
            Y := [];
            for e in E do
                a := NFSeq(e[1],e[2],e[5]);
                xi := EmbeddedCharacter (chi,k,a);
                v := [Eltseq(xi(n)):n in u];
                Append(~X,<u,v>);
                Append(~Y,<u,#v eq 0 select v else [Eltseq(r):r in Rows(Matrix(Rationals(),v)*Matrix(Rationals(),e[2])^-1)]>);
            end for;
            r[10] := sprint([Append(E[i],Y[i]):i in [1..#E]]);
            assert #X eq #F;
            Append(~r,sprint(X));
            Puts(fp,Join(r,":"));
            if not Quiet then printf "Character values for %o:%o:%o computed in %o secs.\n", N,k,o,Cputime()-t; end if;
            cnt +:= 1;
        end if;
    end for;
    if not Quiet then printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start; end if;
end procedure;

function mton(a,mcnt) cnt:=0; for n:=2 to #a do if not a[n] in Rationals() then cnt +:=1; if cnt eq mcnt then return n; end if; end if; end for; assert false; end function;

procedure FixGeneratorBound (infile,outfile:Quiet:=false,Jobs:=1,JobId:=0,SplitInput:=false)
    start := Cputime();
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    if SplitInput and Jobs ne 1 then infile cat:= Sprintf("_%o",JobId); end if;
    S:=Split(Read(infile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S, infile; end if;
    fp := Open(outfile,"w");
    n := 0; cnt := 0;
    for s in S do
        n +:= 1;
        if SplitInput or ((n-JobId) mod Jobs) eq 0 then
            t := Cputime();
            r := Split(s,":");
            if r[10] eq "[]" then Puts(fp,s); cnt +:=1; continue; end if;
            Ein := eval(r[10]); Eout := [];
            for e in Ein do
                a := NFSeq(e[1],e[2],e[5]);
                nn := mton(a,e[7]);
                assert CheckOrderGeneratorBound (e[1], [Eltseq(r) : r in Rows(Matrix(Rationals(),e[5])*Matrix(Rationals(),e[2]))], nn) eq 0;
                Append(~Eout,<e[1],e[2],e[3],e[4],e[5],e[6],nn>);
            end for;
            r[10] := sprint(Eout);
            Puts(fp,Join(r,":"));
            if not Quiet then printf "Updated generator bounds for %o:%o:%o in %o secs.\n", r[1],r[2],r[3],Cputime()-t; end if;
            cnt +:= 1;
        end if;
    end for;
    Flush(fp);
    if not Quiet then printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start; end if;
end procedure;

procedure FixFactorization (infile,outfile,factorfile:Quiet:=false,Jobs:=1,JobId:=0,SplitInput:=false)
    start := Cputime();
    T := AssociativeArray(Integers());
    X := [Split(r,":"):r in Split(Read(factorfile),"\n")];
    for r in X do T[StringToInteger(r[1])] := eval(r[2]); end for;
    tT := Universe(eval(X[1][2]));
    printf "Loaded %o records from factorization file %o\n", #T, factorfile;
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    if SplitInput and Jobs ne 1 then infile cat:= Sprintf("_%o",JobId); end if;
    S:=Split(Read(infile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S, infile; end if;
    fp := Open(outfile,"w");
    n := 0; cnt := 0;
    for s in S do
        n +:= 1;
        if SplitInput or ((n-JobId) mod Jobs) eq 0 then
            t := Cputime();
            r := Split(s,":");
            if r[10] eq "[]" then Puts(fp,s); cnt +:= 1; continue; end if;
            E := eval(r[10]);
            EE := [];
            for i:=1 to #E do
                e := E[i];
                assert #e eq 7;
                if Type(e[4]) eq RngIntElt then
                    if e[4] ne 0 then 
                        printf "updating %o\n", e[4];
                        assert IsDefined(T,e[4]);
                    end if;
                    e := <e[1],e[2],e[3],<e[4],e[4] ne 0 select T[e[4]] else [tT|]>,e[5],e[6],e[7]>;
                end if;
                EE[i] := e;
            end for;
            r[10] := sprint(EE);
            Puts(fp,Join(r,":"));
            cnt +:= 1;
        end if;
    end for;
    Flush(fp);
    if not Quiet then printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start; end if;
end procedure;

procedure FixFactorizationFromData (oldfile,newfile,outfile:Quiet:=false,JobId:="")
    start := Cputime();
    if #JobId gt 0 then
        oldfile cat:= Sprintf("_%o",JobId);
        newfile cat:= Sprintf("_%o",JobId);
        outfile cat:= Sprintf("_%o",JobId);
    end if;
    S1:=Split(Read(oldfile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S1, oldfile; end if;
    S2:=Split(Read(newfile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S2, newfile; end if;
    assert #S1 eq #S2;
    fp := Open(outfile,"w");
    n := 0; cnt := 0;
    for i:=1 to #S1 do
        if S1[i] eq S2[i] then Puts(fp,S2[i]); cnt +:= 1; continue; end if;
        r1 := Split(S1[i],":");  r2 := Split(S2[i],":");
        assert #r1 eq #r2;
        if not Quiet then printf "Checking space %o:%o:%o:%o\n",r1[1],r1[2],r1[3],r1[5]; end if;
        E1 := eval(r1[10]);
        E2 := eval(r2[10]);
        assert #E1 ne 0;
        assert #E2 eq #E1;
        EE := [];
        for i:=1 to #E1 do
            e1 := E1[i];  e2 := E2[i];
            assert #e1 eq 7;
            assert #e2 eq 7;
            if Type(e2[4]) eq RngIntElt then
                assert e2[4] eq e1[4][1];
                e := <e2[1],e2[2],e2[3],e1[4],e2[5],e2[6],e2[7]>;
            else
                e := e2;
            end if;
            EE[i] := e;
        end for;
        r2[10] := sprint(EE);
        s2 := Join(r2,":");
        assert CompareSpaceData(S1[i],s2) eq 0;
        Puts(fp,s2);
        cnt +:= 1;
    end for;
    Flush(fp);
    if not Quiet then printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start; end if;
end procedure;

procedure DumpNFPolys (infile,outfile:Quiet:=false,Jobs:=1,JobId:=0,SplitInput:=false)
    start := Cputime();
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    if SplitInput and Jobs ne 1 then infile cat:= Sprintf("_%o",JobId); end if;
    S:=Split(Read(infile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S, infile; end if;
    fp := Open(outfile,"w");
    n := 0; cnt := 0;
    for s in S do
        n +:= 1;
        if SplitInput or ((n-JobId) mod Jobs) eq 0 then
            t := Cputime();
            r := Split(s,":");
            if r[10] eq "[]" then continue; end if;
            F := eval(r[8]);
            E := eval(r[10]);
            pra := eval(r[13]);
            assert #pra eq #F;
            off := #[f:f in F|#f eq 2];
            assert off + #E le #F;
            for i:=1 to #E do
                assert E[i][1] eq F[off+i];
                assert #E[i][4] eq 2;
                b := pra[off+i];
                d := E[i][4][1]; dfac := E[i][4][2];
                assert b eq 0 or d ne 0;
                assert d eq 0 or #dfac gt 0;
                Puts(fp,strip(Sprintf("%o:%o:%o:%o:%o:%o:%o:%o",r[1],r[2],r[3],off+i,E[i][1],b select E[i][1] else [],d,dfac)));
                cnt +:= 1;
            end for;
            Flush(fp);
        end if;
    end for;
    Flush(fp);
    if not Quiet then printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start; end if;
end procedure;

// merges infile and repfile into outfile with repfile taking precedence (every space in repfile must be already be present in infile)
procedure ReplaceRecords (infile,repfile,outfile)
    S := Split(Read(infile),"\n");
    T := Split(Read(repfile),"\n");
    A := AssociativeArray();
    for r in T do rr := Split(r,":"); A[[StringToInteger(rr[1]),StringToInteger(rr[2]),StringToInteger(rr[3])]] := r; end for;
    fp := Open(outfile,"w");
    keys := [];
    for r in S do
        rr := Split(r,":");
        key := [StringToInteger(rr[1]),StringToInteger(rr[2]),StringToInteger(rr[3])];
        Append(~keys,key);
        if IsDefined(A,key) then Puts(fp,A[key]); Remove(~A,key); printf "Replaced record %o:%o:%o\n",key[1],key[2],key[3]; else Puts(fp,r); end if;
    end for;
    assert #keys eq #Set(keys);
    assert #Keys(A) eq 0;
    Flush(fp);
    printf "Write %o records to %o\n", #keys, outfile;
end procedure;

// space record format is N:k:o:time:dim/dims:trace/traces:ALsigns:Fields:Cutters
// dim/dims may be an integer (dimension of newspace) or a list of integers (dimensions of newforms in the space)
// trace/traces may be a list of integers (traceform of the space) or a list of lists of integers (traceforms of the newforms in the space)
// replaces/updates data from infile1 with data from infile2
procedure MergeSpaceData (infile1, infile2, outfile:StraceUpdate:=false)
    t := Cputime();  start := t;
    S := [Split(r,":"):r in Split(Read(infile1),"\n")];
    X := AssociativeArray(); 
    for i:=1 to #S do r := S[i]; assert not IsDefined(X,r[1..3]); X[r[1..3]] := i; end for;
    printf "Loaded %o records from file %o in %.3os\n", #S, infile1, Cputime()-t;
    t := Cputime();
    T := [Split(r,":"):r in Split(Read(infile2),"\n")];
    printf "Loaded %o records from file %o in %.3os\n", #T, infile2, Cputime()-t;
    fp := Open(outfile,"w");
    cnt := 0;
    for j:=1 to #T do
        r := T[j];
        // if inputfile2 containst space traces, grab dim from trace of a[1]
        if StraceUpdate then r := [r[1],r[2],r[3],r[4],r[5][2..Index(r[5],",")-1],r[5]]; end if;
        i := X[r[1..3]];
        s:= S[i];
        // if record is identical except for timing
        if r eq s then continue; end if;
        if #r eq #s and [r[i]: i in [1..#r]|i ne 4] eq [r[i]:i in [1..#s]|i ne 4] then
            S[i] := r; printf "Updating timing for space %o:%o:%o\n",r[1],r[2],r[3]; continue;
        end if;
        if #r lt 5 then continue; end if;
        if #s lt 5 then S[i] := r; cnt +:= 1; printf "Updated data for space %o:%o:%o (now has %o fields)\n",r[1],r[2],r[3],#S[i];  continue; end if;
        Dr := eval(r[5]);  dimr := Type(Dr) eq SeqEnum select sum(Dr) else Dr;
        Ds := eval(s[5]);  dims := Type(Ds) eq SeqEnum select sum(Ds) else Ds;
        if dimr ne dims then printf "Dr = %o, Ds = %o, dimr = %o, dims = %o\n", Dr, Ds, dimr, dims; end if;
        assert dimr eq dims;
        if Type(Dr) eq SeqEnum then s[5] := r[5]; end if;
        if #r ge 6 then
            if #s lt 6 then s[6] := r[6]; for i:=7 to #r do s[i] := r[i]; end for; end if;
            Tr := eval(r[6]);  tr := #Tr gt 0 and Type(Tr[1]) eq SeqEnum select [sum([Tr[i][j]:i in [1..#Tr]]):j in [1..#Tr[1]]] else Tr;
            Ts := eval(s[6]);  ts := #Ts gt 0 and Type(Ts[1]) eq SeqEnum select [sum([Ts[i][j]:i in [1..#Ts]]):j in [1..#Ts[1]]] else Ts;
            n := Min(#tr,#ts);
            assert tr[1..n] eq ts[1..n];
            if (#Tr gt 0 and Type(Tr[1]) eq SeqEnum) or #tr gt #ts then s[6] := r[6]; end if;
            for i:=7 to #r do s[i] := r[i]; end for;
        end if;
        if S[i] ne s then S[i] := s; cnt +:= 1; printf "Updated data for space %o:%o:%o (now has %o fields)\n",r[1],r[2],r[3],#S[i]; end if;
    end for;
    for r in S do Puts(fp,Join(r,":")); end for;
    Flush(fp);
    printf "Wrote %o records (%o updated) to file %o, total time %.3os\n", #S, cnt, outfile, Cputime()-start;
end procedure;

Attach("polredabs.m");
Attach("chars.m");
Attach("zbasis.m");
Attach("mfchars.m");
Attach("mfdims.m");
Attach("hash.m");

function sum(X) return #X eq 0 select 0 else &+X; end function;
function strip(X) return Join(Split(Join(Split(X," "),""),"\n"),""); end function;
function sprint(X) return strip(Sprintf("%o",X)); end function;

// Number of newspaces N.k.x with k >= 2 an Nk^2 <= B (some of which may be emptry)
function NumberOfNewspaces(B)
    return &+[NumberOfCharacterOrbits(N)*(Floor(Sqrt(B/N))-1):N in [1..Floor(B/4)]];
end function;

function NewspaceDimension (chi, k)
    return Dimension(NewSubspace(CuspidalSubspace(ModularForms(chi,k))));
end function;

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

// Given a list of cutters recontstructs the corresponding subspace of modular symbols for the specifiec character chi and weight k
function ReconstructNewspaceComponent(chi,k,cutters)
    if #cutters gt 0 and Type(cutters[1][2]) eq SeqEnum then
        R<x>:=PolynomialRing(Rationals());
        cutters := [<a[1],R!a[2]>:a in cutters];
    end if;
    return Kernel(cutters,NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1))));
end function;

// Given a list of Hecke orbits in a newspace compute a list of cutters that can be used to reconstruct them    
function ComputeCutters (S)
    num := #S;
    HC := [[]:i in [1..num]];
    if num le 1 then return HC; end if;
    N := Level(S[1]);
    n := 1;  p := 1;
    while true do
        p := NextPrime(p);
        if N mod p ne 0 then
            for i:=1 to num do
                // We could use MinimalPolynomial, but we would still need to factor its Norm
                g := Norm(CharacteristicPolynomial(HeckeOperator(S[i],p)));
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
function MinimizeCutters (HC)
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

// Given a list of ap's for primes p up to at least 2^13 for a motive of weight w (where w=k-1 for modular forms)
// returns the trace zero density, a list of trace moments, and the trash hash (as defined in https://doi.org/10.1112/S146115701600019X)
function TraceStats(aplist, w : Moments:= 6)
    assert #aplist ge 1028;  // need at least the 1028 primes up to 2^13
    h := TraceHash(aplist);
    z := 1.0*#[a:a in aplist|a eq 0]/#aplist;
    // normalize traces
    P := PrimesInInterval(1,NthPrime(#aplist));
    e := w/2;
    a := [aplist[i]/P[i]^e:i in [1..#aplist]];
    m := [&+[t^n:t in a]/#a:n in [1..Moments]];
    return z,m,h;
end function;
    
/*
Format of mfdata_B.m.txt is N:k:i:t:D:T:A:F:C:E:cm:itwists:ispolredabs:zratios:zmoments:tracehashes where B is an upper bound on Nk^2.
The data depends on a degree bound (currently 20), and a coefficient index bound (currently 1000).

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
cm = list of cm discriminants, one for each subspace listed in D up to the degree bound, 0 indicates non-CM forms (rigorous)
itwists = list of lists of char orbits of non-trivial inner twists for spaces of dimension up to the degree bound (not rigorous!)
ispolredabs = list of boolean values (0 or 1) such that pra[i] is 1 if F[i] is the polredabs polynomial for the Hecke field
zratios = list of proportions of zero a_p over primes p < 2^13 (decimal number), one for each subspace
zmoments = list of list of moments of normalized a_p over primes p < 2^13 (decimal numbers), one for each subspace
tracehashes = list of trace hashes (linear combination of tr(a_p) over p in [2^12,2^13] mod 2^61-1), one for subspace
*/

function NewspaceData (G, k, o: OrbitRepTable:=AssociativeArray(), TraceHint:=[], NoCM:=false,
                       ComputeTraces:=false, ComputeEigenvalues:=false, ComputeTraceStats:=false, NumberOfCoefficients:=0, DegreeBound:=0, Detail:=0)
    st := Cputime();
    chi := G[o];  N := Modulus(chi);
    dNS := QDimensionNewCuspForms(chi,k);
    if dNS eq 0 then
        if Detail gt 0 then printf "The space %o:%o:%o is empty\n",N,k,o; end if;
        s := Sprintf("%o:%o:%o:%o:%o:[]:[]:[]:[]:[]:[]:[]:[]", N, k, o, Cputime()-st, []);
        if ComputeTraceStats then s cat:= ":[]:[]:[]"; end if;
        return strip(s);
    end if;
    if ComputeEigenvalues then ComputeTraces := true; end if;
    if #TraceHint gt 0 then ComputeTraces := true; end if;
    if Detail gt 0 then printf "Constructing space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
    NS := NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1)));
    if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
    n := Max(HeckeBound(NS)+10,NumberOfCoefficients);
    assert dNS eq Degree(chi)*Dimension(NS);
    if #TraceHint gt 0 then
        assert &and[t[1] ge 1:t in TraceHint] and &+[t[1]:t in TraceHint] eq dNS;
        assert #Set([#t:t in TraceHint]) eq 1;
        TraceHint := Sort(TraceHint);
        if #TraceHint[1] lt n then
            printf "*** Warning: ignoring TraceHint because it contains only %o < %o traces! ***", #TraceHint[1], n;
            TraceHint := [];
        end if;
        if #TraceHint eq 1 and DegreeBound gt 0 and dNS gt DegreeBound then
            if Detail gt 0 then printf "TraceHint implies that the space %o:%o:%o consists of a single orbit of dimension %o\n",N,k,o,dNS; end if;
            if Detail gt 0 and Order(chi) eq 1 then printf "Computing Atkin-Lehner signs for space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
            AL := Order(chi) eq 1 select [[<p,ExactQuotient(Trace(AtkinLehnerOperator(NS,p)),dNS)>:p in PrimeDivisors(N)]] else [];
            if Detail gt 0 and Order(chi) eq 1 then printf "took %o secs.\n", Cputime()-t; printf "Atkin-Lehner signs %o\n", sprint(AL); end if;
            s := Sprintf("%o:%o:%o:%o:%o:%o:%o:[]:[[]]:[]:[]:[]:[]", N, k, o, Cputime()-st, [dNS], TraceHint, AL);
            if ComputeTraceStats then s cat:= ":[]:[]:[]"; end if;
            return strip(s);
        end if;
    end if;
    if Detail gt 0 then printf "Decomposing space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
    S := NewformDecomposition(NS);
    if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
    D := [Degree(chi)*Dimension(S[i]): i in [1..#S]];
    if DegreeBound eq 0 then DegreeBound := Max(D); end if;
    if Detail gt 0 then printf "dims = %o\n", sprint(D); end if;
    if ComputeTraces or #Set(D) ne #D then
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
    else
        // When dimensions are distinct, it suffices to sort eigenforms by dimension, we don't need to compute traces to do this
        TT := Sort([[D[i],i] : i in [1..#D]]);
        D := [D[TT[i][2]] : i in [1..#TT]];  S := [S[TT[i][2]] : i in [1..#TT]];
        T := [];
    end if;
    if Detail gt 0 and Order(chi) eq 1 then printf "Computing Atkin-Lehner signs for space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
    AL := Order(chi) eq 1 select [[<p,ExactQuotient(Trace(AtkinLehnerOperator(S[i],p)),D[i])>:p in PrimeDivisors(N)]:i in [1..#S]] else [];
    if Detail gt 0 and Order(chi) eq 1 then printf "took %o secs.\n", Cputime()-t; printf "Atkin-Lehner signs %o\n", sprint(AL); end if;
    if #[d:d in D|d le DegreeBound] gt 0 then
        HC:=[[]:d in D];   
        if #D gt 1 then
            if Detail gt 0 then printf "Computing Hecke cutters for space %o:%o:%o...",N,k,o; t:=Cputime(); end if;
            HC := ComputeCutters(S);
            if Detail gt 0 then printf "cutter length %o, took %o secs\n", #HC[1], Cputime()-t; end if;
        end if;
    else
        HC := [];
    end if;
    u := UnitGenerators(chi);
    HF := []; E := []; cm := []; it := []; X := [];
    if ComputeEigenvalues then
        R<x> := PolynomialRing(Rationals());
        HF := [[0,1]:d in D|d eq 1]; pra:=[1:i in [1..#HF]];
        X := [<u,[Eltseq(v):v in ValuesOnUnitGenerators(chi)]>:d in D|d eq 1];
        if #[d:d in D|d gt 1 and d le DegreeBound] gt 0 then
            if Detail gt 0 then printf "Computing %o exact Hecke eigenvalues with degreebound %o for space %o:%o:%o...",n,DegreeBound,N,k,o; t:=Cputime(); end if;
            for i:=1 to #F do
                if D[i] gt 1 and D[i] le DegreeBound then
                    K := AbsoluteField(BaseRing(Parent(F[i])));
                    f,b,a,c,d,pr := OptimizedOrderBasis(Eltseq(MinimalPolynomial(K.1)),[Eltseq(K!Coefficient(F[i],j)) : j in [1..n]]);
                    v := #u gt 0 select [Eltseq(z):z in EmbeddedCharacterValuesOnUnitGenerators(chi,k,NFSeq(f,b,a))] else [];
                    w := #u gt 0 select [Eltseq(r):r in Rows(Matrix(Rationals(),v)*Matrix(Rationals(),b)^-1)] else [];
                    Append(~E,<f,b,c,d eq 0 select 0 else 1,a,<u,w>>);  Append(~pra,pr select 1 else 0);  Append(~HF,f);  Append(~X,<u,v>);
                end if;
            end for;
            if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
        end if;
        if not NoCM then
            if Detail gt 0 then printf "Finding CM forms in space %o:%o:%o...",N,k,o; t:=Cputime(); end if;
            cm := [a select b else 0 where a,b:=IsCM(S[i]:Proof:=true):i in [1..#S]|D[i] le DegreeBound];
            if Detail gt 0 then printf "took %o secs\n", Cputime()-t; printf "CM discriminants: %o\n", sprint(cm); end if;
            if Detail gt 0 then printf "Finding inner twists in space %o:%o:%o...",N,k,o; t:=Cputime(); end if;
            if #Keys(OrbitRepTable) eq 0 then _,OrbitRepTable := CharacterOrbitReps (N:RepTable:=true); end if;
            it := [cm[i] eq 0 select [OrbitRepTable[chi]:chi in t|Order(chi) gt 1] where t:= InnerTwists(S[i]) else [] :i in [1..#S]|D[i] le DegreeBound];
            if Detail gt 0 then printf "took %o secs\n", Cputime()-t; printf "Inner twists: %o\n", sprint(it); end if;
        end if;
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
    s := Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-st, D);
    s cat:= Sprintf(":%o:%o:%o:%o",T,AL,HF,HC);
    if ComputeEigenvalues then s cat:= Sprintf(":%o:%o:%o:%o",E,cm,it,pra); else s cat:= ":[]:[]:[]:[]"; end if;
    if ComputeTraceStats then s cat:= Sprintf(":%o:%o:%o", Z, M, H); else s cat:= ":[]:[]:[]"; end if;
    s cat:= Sprintf(":%o",X);
    return strip(s);
end function;

procedure ValidateSpaceData (s:Coeffs:=1000,DegBound:=20,CharTable:=[])
    assert Coeffs gt 0;
    R<x>:=PolynomialRing(Integers());
    r := Split(s,":");
    N := StringToInteger(r[1]); k := StringToInteger(r[2]); o := StringToInteger(r[3]);
    D := eval(r[5]); T := eval(r[6]); A := eval(r[7]); HF := eval(r[8]); HC := eval(r[9]); E := eval(r[10]); cm := eval(r[11]); twists := eval(r[12]); pra := eval(r[13]);
    if #r gt 13 then zratio := eval(r[14]); zmoments := eval(r[15]); hash := eval(r[16]); else zratio := []; zmoments := []; hash := []; end if;
    if #r gt 16 then X := eval(r[17]); else X := []; end if;
    assert N gt 0 and k gt 0 and o gt 0;
    G := N le #CharTable select CharTable[N] else CharacterOrbitReps(N);
    assert o le #G;
    chi := G[o];    dchi := Degree(chi);
    // Check that D is a sorted list of integers whose sum is the dimension of the newspace (last condiction verified only for wt k>1) and that each d in D is divisible by the degree of Q(chi)
    assert Type(D) eq SeqEnum;
    if k gt 1 then assert sum(D) eq QDimensionNewCuspForms(chi,k); end if;
    if #D gt 0 then assert &and[Type(d) eq RngIntElt and d gt 0 and IsDivisibleBy(d,dchi):d in D]; end if;
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
    assert (k eq 1 and #HC eq 0) or (#HC eq #D and #Set(HC) eq #D);
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
        assert e[4] eq 0 or e[4] eq 1;
        assert Type(e[5]) eq SeqEnum and Type(e[5][1]) eq SeqEnum and Type(e[5][1][1]) eq RngIntElt;
        assert #e[5] ge Coeffs and #e[5] le #T[off+i] and {#c:c in e[5]} eq {d};
        // Verify that traces match
        a := NFSeq(e[1],e[2],e[5]);
        assert [Trace(c):c in a] eq [T[off+i][n]:n in [1..#e[5]]];
        // Check character values if present
        if #e gt 5 then assert n eq o where _,n := CharacterFromValues(N,e[6][1],NFSeq(e[1],e[2],e[6][2]):Orbit); end if;
    end for;
    // For k > 1 check that cm is a list of non-positive integers of with an entry for each d in D up to DegBound (if nonzero, the discriminant of an imaginary quadratic field)
    assert Type(cm) eq SeqEnum and ((k eq 1 and #cm eq 0) or #cm ge #[d:d in D|d le DegBound]);
    if #cm gt 0 then assert &and[Type(n) eq RngIntElt and n le 0 and (n eq 0 or IsDiscriminant(n)):n in cm]; end if;
    // For k > 1 check that twists is a list of lists of integers identifying character orbits of non-trivial inner twists for each d in D up to DegBound (empty lists means no non-trivial inner twist)
    assert Type(twists) eq SeqEnum and ((k eq 1 and #twists eq 0) or #twists ge #[d:d in D|d le DegBound]);
    if #twists gt 0 then assert &and[Type(t) eq SeqEnum : t in twists]; assert &and[&and[Type(n) eq RngIntElt and n gt 0 and n le NumberOfCharacterOrbits(N) : n in t]:t in twists|#t gt 0]; end if;
    // Check that pra is a list of integers 0 or 1, one for each polynomial in HF
    assert Type(pra) eq SeqEnum and #pra eq #HF and Set(pra) subset {0,1};
    // If non-empty, check that zratios is a list of real numbers in [0,1]
    assert Type(zratio) eq SeqEnum;
    if #zratio gt 0 then assert #zratio le #D and &and[r ge 0.0 and r le 1.0:r in zratio]; end if;
    // If non-empty check that zmoments is a list of lists of real numbers (moments of normalized traces)
    assert Type(zmoments) eq SeqEnum;
    if #zmoments gt 0 then assert #zmoments le #D and &and[Type(m) eq SeqEnum and Type(m[1]) eq FldReElt:m in zmoments]; end if;
    // For k > 1 check that hash is a list of integers in [0,2^61-1], one for each d in D up to DegBound
    assert Type(hash) eq SeqEnum and ((k eq 1 and #hash eq 0) or #hash ge #[d:d in D|d le DegBound]);
    if #hash gt 0 then assert &and[Type(h) eq RngIntElt and h ge 0 and h lt 2^61-1:h in hash]; end if;
    assert Type(X) eq SeqEnum;
    if #X ne 0 then assert #X eq #HF; end if;
    for i:= 1 to #X do assert n eq o where _,n := CharacterFromValues (N,X[i][1],[K|x:x in X[i][2]]:Orbit) where K:=NumberField(R!HF[i]); end for;
end procedure;

procedure ValidateDataFile (infile:Quiet:=false,Jobs:=1,JobId:=0)
    start := Cputime();
    S:=Split(Read(infile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S, infile; end if;
    n := 0;
    for s in S do
        n +:= 1;
        if ((n-JobId) mod Jobs) eq 0 then
            if not Quiet then t := Cputime(); end if;
            ValidateSpaceData(s);
            if not Quiet then printf "Validated data for %o:%o:%o:%o in %o secs\n", r[1],r[2],r[3],r[5],Cputime()-t where r:=Split(s,":"); end if;
        end if;
    end for;
    printf "Validated %o data records in %o secs\n", n, Cputime()-start;
end procedure;

// Decompose spaces S_k(N,chi)^new into Galois stable subspaces for k*N <= B
procedure DecomposeSpaces (outfile,B:TodoFile:="",Quiet:=false,DimensionsOnly:=false,Coeffs:=1000,DegBound:=20,TrivialCharOnly:=false,TraceStats:=false,Jobs:=1,JobId:=0)
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
    for N:=1 to Floor(B/4) do
        if #L gt 0 and not N in L then continue; end if;
        if not Quiet then printf "Constructing character group data for modulus %o...", N; t:=Cputime(); end if;
        G, T := CharacterOrbitReps(N:RepTable);
        if not Quiet then printf "took %o secs\n",Cputime()-t; end if;
        for k := 2 to Floor(Sqrt(B/N)) do
            for o in [1..#G] do
                if o gt 1 and TrivialCharOnly then break; end if;
                if #L gt 0 and not IsDefined(TodoList,[N,k,o]) then continue; end if;
                hint := #L gt 0 select TodoList[[N,k,o]] else [];
                n +:= 1;
                if ((n-JobId) mod Jobs) eq 0 then
                    if DimensionsOnly then
                        str := NewspaceData(G,k,o:OrbitRepTable:=T,Detail:=Quiet select 0 else 1);
                    else
                        if not Quiet then printf "Processing space %o:%o:%o with coeffs %o, deg-bound %o\n", N,k,o, Coeffs, DegBound; t:=Cputime(); end if;
                        str := NewspaceData(G,k,o:OrbitRepTable:=T,TraceHint:=hint,ComputeTraces,NumberOfCoefficients:=Coeffs,ComputeEigenvalues,ComputeTraceStats:=TraceStats,DegreeBound:=DegBound,Detail:=Quiet select 0 else 1);
                        if not Quiet then printf "Total time for space %o:%o:%o was %os\n", N,k,o,Cputime()-t; end if;
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
                    
procedure DecomposeSpacesFixedLevelWeight (outfile,N,k:Quiet:=false,NoCM:=false,DimensionsOnly:=false,Coeffs:=1000,DegBound:=20,TrivialCharOnly:=false)
    st := Cputime();
    n := 0; cnt:=0;
    fp := Open(outfile,"w");
    if not Quiet then printf "Constructing character group data for modulus %o...", N; t:=Cputime(); end if;
    G, T := CharacterOrbitReps(N:RepTable);
    if not Quiet then printf "took %o secs\n",Cputime()-t; end if;
    for o in [1..#G] do
        if o gt 1 and TrivialCharOnly then break; end if;
        n +:= 1;
        if DimensionsOnly then
            str := NewspaceData(G,k,o:OrbitRepTable:=T,Detail:=Quiet select 0 else 1);
        else
            if not Quiet then printf "Processing space %o:%o:%o with coeffs %o, deg-bound %o\n", N,k,o, Coeffs, DegBound; t:=Cputime(); end if;
            str := NewspaceData(G,k,o:OrbitRepTable:=T,ComputeTraces,NoCM:=NoCM,NumberOfCoefficients:=Coeffs,ComputeEigenvalues,ComputeTraceStats,DegreeBound:=DegBound,Detail:=Quiet select 0 else 1);
            if not Quiet then printf "Total time for space %o:%o:%o was %os\n", N,k,o,Cputime()-t; end if;
        end if;
        Puts(fp,str);
        Flush(fp);
        cnt +:= 1;
    end for;
    printf "Wrote %o records to %o using %os of CPU time.\n", cnt, outfile, Cputime()-st;
end procedure;

procedure ProcessPariGPData (infile,outfile:Quiet:=false,Jobs:=1,JobId:=0)
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    S:=Split(Read(infile),"\n");
    if not Quiet then printf "Loaded %o records from %o\n", #S, infile; end if;
    fp := Open(outfile,"w");
    n := 0; cnt := 0;
    for s in S do
        n +:= 1;
        if ((n-JobId) mod Jobs) eq 0 then
            r := Split(s,":");
            D := eval(r[5]);
            inE := eval(r[10]);
            inHF := eval(r[8]);
            HF:=[[0,1]:i in [1..#D]|D[i] eq 1];  E:=[];  pra:=[1:i in [1..#HF]];
            for e in inE do
                c := [Eltseq(a):a in Rows(Matrix(Rationals(),e[5])*Matrix(Rationals(),e[2]))];
                f,b,c,u,d,pr := OptimizedOrderBasis([Rationals()!a:a in e[1]],c);
                Append(~E,<f,b,u,d eq 0 select 0 else 1,c>);  Append(~pra,pr select 1 else 0);  Append(~HF,f);
            end for;
            assert #E eq #inE;
            assert #HF eq #pra;
            Puts(fp,strip(Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:[]:[]:[]",r[1],r[2],r[3],r[4],r[5],r[6],r[7],HF,r[9],E,r[11],r[12],pra)));
            Flush(fp);
            cnt +:= 1;
            if not Quiet then printf "%o:%o:%o:%o\n",r[1],r[2],r[3],r[5]; end if;
        end if;
    end for;
    if not Quiet then printf "Wrote %o records to %\o\n", #S, outfile; end if;
end procedure;

procedure PolredabsFixup (infile,polredabsfile,outfile,noprafile)
    S := [Split(r,":"):r in Split(Read(polredabsfile),"\n")];
    A:=AssociativeArray();
    for s in S do A[eval(s[1])] := eval(s[2]); end for;
    printf "Loaded %o polredabs polys from %o\n", #Keys(A), polredabsfile;
    start := Cputime();
    S:=Split(Read(infile),"\n");
    printf "Loaded %o data records from %o in %o secs\n", #S, infile, Cputime()-start;
    start := Cputime();
    fp := Open(outfile,"w");
    noprafp := Open(noprafile,"w");
    B := {};
    m := 0; n := 0;
    for s in S do
        r := Split(s,":");
        if r[13] eq "[]" then n +:= 1; Puts(fp,s); continue; end if;
        pra := eval(r[13]);
        if not 0 in pra then n +:= 1; Puts(fp,s); continue; end if;
        D := eval(r[5]);
        F := eval(r[8]);
        E := eval(r[10]);
        off := #[d:d in D|d eq 1];
        update := false;
        for i in [1..#pra] do
            if pra[i] eq 0 then
                if IsDefined(A,F[i]) then
                    newf := A[F[i]];
                    if newf eq F[i] then
                        printf "Setting polredabs flag for %o:%o:%o:%o...\n", r[1],r[2],r[3],i;  t:=Cputime();
                        pra[i]:=1;
                        update := true;
                        continue;
                    end if;
                    printf "Updating data for %o:%o:%o:%o...\n", r[1],r[2],r[3],i;  t:=Cputime();
                    e := E[i-off];
                    assert e[1] eq F[i];
                    c := [Eltseq(a):a in Rows(Matrix(Rationals(),e[5])*Matrix(Rationals(),e[2]))];
                    f,b,c,u,d,pr := OptimizedOrderBasis([Rationals()!a:a in e[1]],c:PolredabsPoly:=newf);
                    assert f eq newf and pr;
                    assert NFSeqIsIsomorphic(NFSeq(e[1],e[2],e[5]),NFSeq(f,b,c));
                    F[i] := f;
                    E[i-off] := <f,b,u,d eq 0 select 0 else 1,c>;
                    pra[i] := 1;
                    printf "Update took %o secs\n", Cputime()-t;
                    update := true;
                else
                    if not F[i] in B then
                        Puts(noprafp,sprint(F[i]));
                        Include(~B,F[i]);
                        m +:=1;
                    end if;
                end if;
            end if;
        end for;
        n +:= 1;
        if update then
            r[8] := sprint(F);
            r[10] := sprint(E);
            r[13] := sprint(pra);
            Puts(fp,Join(r,":"));
        else
            Puts(fp,s);
        end if;
    end for;
    printf "Wrote %o non-polredabs polys to %o\n", m, noprafile;
    printf "Wrote %o records to %o in %o secs\n", n, outfile, Cputime()-start;
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
    if not Quiet then printf "Wrote %o records to %\o in %o secs\n", cnt, outfile, Cputime()-start; end if;
end procedure;

function CompareRecords(s1,s2:TracesOnly:=false)
    r1 := Split(strip(s1),":"); r2 := Split(strip(s2),":");
    if #r1 eq #r2 and [r1[i]:i in [1..#r1]|i ne 4] eq [r2[i]:i in [1..#r2]|i ne 4] then return true; end if;
    minfields := TracesOnly select 6 else 10;
    if #r1 lt minfields then printf "Only %o fields in r1, expected at least %o!\n", #r1, minfields; return false; end if;
    if #r2 lt minfields then printf "Only %o fields in r2, expected at least %o!\n", #r2, minfields; return false; end if;
    if r1[1] ne r2[1] then printf "Level %o != %o\n", r1[1], r2[1]; return false; end if;
    if r1[2] ne r2[2] then printf "Weight %o != %o\n", r1[2], r2[2]; return false; end if;
    if r1[3] ne r2[3] then printf "CharOrbit %o != %o\n", r1[3], r2[3]; return false; end if;
    if r1[5] ne r2[5] then printf "Dimensions %o != %o\n", r1[5], r2[5]; return false; end if;
    if r1[6] ne r2[6] then
        traces1 := eval(r1[6]); traces2 := eval(r2[6]);
        if #traces1 ne #traces2 then printf "Number of trace vectors %o != %o\n", #traces1, #traces2; return false; end if;
        if [#t:t in traces1] ne [#t:t in traces2] then "Number of traces %o != %o\n", [#t:t in traces1], [#t:t in traces2]; return false; end if;
        for i:= 1 to #traces1 do
            for j:=1 to #traces1[i] do
                if traces1[i][j] ne traces2[i][j] then printf "Traces %o != %o disagree for a_%o in trace vector %o\n", traces1[i][j], traces2[i][j], j, i; return false; end if;
            end for;
        end for;
        printf "Wierdness! Trace mismatch!\n"; return false;
    end if;
    if TracesOnly then return true; end if;
    if r1[7] ne r2[7] then printf "Atkin-Lehner signs %o != %o\n", r1[7], r2[7]; return false; end if;
    if r1[8] ne r2[8] then
        f1 := eval(r1[8]); f2 := eval(r2[8]);
        if #f1 ne #f2 then printf "Different number of field polys\n"; return false; end if;
        for i:=1 to #f1 do
            if not NFPolyIsIsomorphic(f1[i],f2[i]) then printf "Coefficient field polys %o != %o do not define the same field\n", f1[i], f2[i]; return false; end if;
        end for;
    end if;
    if r1[10] ne r2[10] then
        E1 := eval(r1[10]); E2 := eval(r2[10]);
        if #E1 ne #E2 then printf "Number of eigenvalue vectors %o != %o\n", #E1, #E2; return false; end if;
        for i:=1 to #E1 do
//t := Cputime();
//printf "Checking eigenvalues for %o:%o:%o:%o:[%o] (current memory %o MB)...\n", r1[1],r1[2],r1[3],i,#E1[i][1]-1,Round(GetMemoryUsage()/2^20);
            if not NFPolyIsIsomorphic(E1[i][1],E2[i][1]) then printf "Coefficient field polys %o != %o do not define the same field\n", E1[i][1], E2[i][1]; return false; end if;
            C1 := [Eltseq(r) : r in Rows(Matrix(Rationals(),E1[i][5])*Matrix(Rationals(),E1[i][2]))];
            C2 := [Eltseq(r) : r in Rows(Matrix(Rationals(),E2[i][5])*Matrix(Rationals(),E2[i][2]))];
            if #C1 ne #C2 then printf "Different number %o != %o of eigenvalues in entry %o\n", #C1, #C2, i; end if;
            m := Min(#C1,#C2); C1 := [C1[j]:j in [1..m]]; C2 := [C2[j]:j in [1..m]];
            if not NFSeqIsIsomorphic(E1[i][1],C1,E2[i][1],C2) then printf "Eigenvalue mismatch for entry %o\n", i; return false; end if;
//printf "Checked eigenvalues for %o:%o:%o:%o:[%o] using %o secs (current memory %o MB)\n", r1[1],r1[2],r1[3],i,#E1[i][1]-1,Cputime()-t,Round(GetMemoryUsage()/2^20);
            if #E1[i] gt 5 and #E2[i] gt 5 then
                C1 := [Eltseq(r) : r in Rows(Matrix(Rationals(),E1[i][5])*Matrix(Rationals(),E1[i][6][2]))];
                C2 := [Eltseq(r) : r in Rows(Matrix(Rationals(),E2[i][5])*Matrix(Rationals(),E2[i][6][2]))];
                if not NFSeqIsIsomorphic(E1[i][1],C1,E2[i][1],C2) then printf "Character value mismatch for entry %o\n", i; return false; end if;
            end if;
        end for;
    end if;
    return true;
end function;
            
function CompareDataFiles (infile1,infile2:TracesOnly:=false,Quiet:=false,Jobs:=1,JobId:=0)
    start := Cputime();
    S1 := Split(Read(infile1),"\n");
    S2 := Split(Read(infile2),"\n");
    if not Quiet then printf "Loaded %o records from file %o and %o records from file %o in %o secs\n", #S1, infile1, #S2, infile2, Cputime()-start; end if;
    if #S1 ne #S2 then printf "Warning files %o and %o do not have the same number of records: %o vs %o\n", infile1, infile2, #S1, #S2; end if;
    start := Cputime();
    n := Min(#S1,#S2);
    cnt := 0;
    for i:=1 to n do
        if ((i-JobId) mod Jobs) eq 0 then
            cnt +:= 1;
            if S1[i] eq S2[i] then continue; end if;
            t := Cputime();
            if not CompareRecords (S1[i],S2[i]:TracesOnly:=TracesOnly) then print "Mismatch for records at line %o\n", i; return false; end if;
            if not Quiet and Cputime()-t gt 0.1 then printf "Successfully matched distinct records at line %o in %o secs\n", i, Cputime()-t; end if;
        end if;
    end for;
    printf "Succesfully matched %o of %o lines from files %o and %o in %o secs\n", cnt, n, infile1, infile2, Cputime()-start;
    return true;
end function;
        
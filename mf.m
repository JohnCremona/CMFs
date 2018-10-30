Attach("polredabs.m");
Attach("chars.m");
Attach("zbasis.m");
Attach("hash.m");

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

function sum(X) return #X eq 0 select 0 else &+X; end function;
function strip(X) return Join(Split(Join(Split(X," "),""),"\n"),""); end function;
function sprint(X) return strip(Sprintf("%o",X)); end function;

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

/*    
procedure RewriteCutters(infile,outfile:VerificationLimit:=20)
    start := Cputime();
    S:=Split(Read(infile),"\n");
    printf "Loaded %o records from file %o\n", #S, infile;
    outfp := Open(outfile, "w");
    L := [];
    for n:=1 to #S do
        r := Split(S[n],":");
        HC := eval(r[9]);
        NHC := MinimizeCutters(HC);
        L[n] := #NHC gt 0 select #NHC[1] else 0;
        if #NHC gt 0 and #NHC[1] lt #HC[1] then 
            printf "Reduced cutter length for space %o:%o:%o from %o to %o\n", r[1],r[2],r[3],#HC[1],#NHC[1];
            dims := eval(r[5]);
            if &+dims le VerificationLimit then
                printf "Verifing cutters in space with orbit sizes %o\n", dims;
                N := StringToInteger(r[1]); k:=StringToInteger(r[2]); o:=StringToInteger(r[3]);
                chi := CharacterOrbitReps(N)[o];
                time  F := [ReconstructNewspaceComponent(chi,k,cutter):cutter in NHC];
                assert [Dimension(f)*Degree(chi):f in F] eq dims;
                print "Verified!";
            end if;
            r[9] := sprint(NHC);
        end if;
        Puts(outfp,Join(r,":"));
    end for;
    Flush(outfp); delete outfp;
    printf "Wrote %o updated records to file %o in %os\n", #S, outfile, Cputime()-start;
    printf "Cutter length histogram is %o\n", {* n: n in L *};
end procedure;
*/

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
    if ComputeEigenvalues then ComputeTraces := true; end if;
    if #TraceHint gt 0 then ComputeTraces := true; end if;
    chi := G[o];  N := Modulus(chi);
    if Detail gt 0 then printf "Constructing space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
    NS := NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1)));
    if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
    n := Max(HeckeBound(NS)+10,NumberOfCoefficients);
    dNS := Degree(chi)*Dimension(NS);
    if dNS eq 0 then
        if Detail gt 0 then printf "The space %o:%o:%o is empty\n",N,k,o; end if;
        s := Sprintf("%o:%o:%o:%o:%o:[]:[]:[]:[]:[]:[]:[]:[]", N, k, o, Cputime()-st, []);
        if ComputeTraceStats then s cat:= ":[]:[]:[]"; end if;
        return strip(s);
    end if;
    if #TraceHint gt 0 then
        assert &and[t[1] ge 1:t in TraceHint] and &+[t[1]:t in TraceHint] eq dNS;
        assert #Set([#t:t in TraceHint]) eq 1;
        TraceHint := Sort(TraceHint);
        if #TraceHint[1] lt n then
            print "*** Warning: ignoring TraceHint because it contains only %o < %o traces! ***", #TraceHint[1], n;
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
            if Detail gt 0 then printf "Computing labels for forms in space %o:%o:%o using TraceHint...", n, N,k,o; t:=Cputime(); end if;
            DT := [t[1]:t in TraceHint];
            DTM := Multiset([t[1]:t in TraceHint]);  assert Multiset(D) eq DTM;
            F := [* (Multiplicity(DTM,D[i]) gt 1 or (ComputeEigenvalues and D[i] gt 1 and D[i] le DegreeBound)) select Eigenform(S[i],n+1) else 0 : i in [1..#S] *];
            T := [];
            for i := 1 to #S do
                if Multiplicity(DT,D[i]) eq 1 then
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
    HC:=[[]:d in D];   
    if #D gt 1 then
        if Detail gt 0 then printf "Computing Hecke cutters for space %o:%o:%o...",N,k,o; t:=Cputime(); end if;
        HC := ComputeCutters(S);
        if Detail gt 0 then printf "cutter length %o, took %o secs\n", #HC[1], Cputime()-t; end if;
    end if;
    HF := []; E := []; cm := []; it:=[];
    if ComputeEigenvalues then
        HF := [[0,1]:i in [1..#D]|D[i] eq 1];  pra:=[1:i in [1..#HF]];
        if #[d:d in D|d gt 1 and d le DegreeBound] gt 0 then
            if Detail gt 0 then printf "Computing %o exact Hecke eigenvalues with degreebound %o for space %o:%o:%o...",n,DegreeBound,N,k,o; t:=Cputime(); end if;
            for i:=1 to #F do
                if D[i] gt 1 and D[i] le DegreeBound then
                    K := AbsoluteField(BaseRing(Parent(F[i])));
                    f,b,c,u,d,pr := OptimizedOrderBasis(Eltseq(MinimalPolynomial(K.1)),[Eltseq(K!Coefficient(F[i],j)) : j in [1..n]]);
                    Append(~E,<f,b,u,d eq 0 select 0 else 1,c>);  Append(~pra,pr select 1 else 0);  Append(~HF,f);
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
        if Detail gt 0 then printf "Computing trace stats with degreebound %o for space %o:%o:%o...",DegreeBound,N,k,o; t:=Cputime(); end if;
        Z := []; M := []; H:=[];
        for i:=1 to #D do
            if D[i] gt DegreeBound then break; end if;
            z,m,h := TraceStats([Integers()!Trace(Trace(a)):a in SystemOfEigenvalues(S[i],8192)], k-1);
            z := Sprintf("%.3o",z lt 0.001 select 0 else z); m:=[Sprintf("%.3o",x lt 0.001 select 0 else x):x in m]; // trim precision (still ridiculous)
            Append(~Z,z); Append(~M,m); Append(~H,h);
        end for;
        if Detail gt 0 then printf "took %o secs\n", Cputime()-t; printf "Hashes: %o\n", sprint(H); end if;
    end if;
    s := Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-st, D);
    s cat:= Sprintf(":%o:%o:%o:%o",T,AL,HF,HC);
    if ComputeEigenvalues then s cat:= Sprintf(":%o:%o:%o:%o",E,cm,it,pra); else s cat:= ":[]:[]:[]:[]"; end if;
    if ComputeTraceStats then s cat:= Sprintf(":%o:%o:%o", Z, M, H); end if;
    return strip(s);
end function;

// Decompose spaces S_k(N,chi)^new into Galois stable subspaces for k*N <= B
procedure DecomposeSpaces (outfile,B:TodoFile:="",Quiet:=false,DimensionsOnly:=false,Coeffs:=1000,DegBound:=20,TrivialCharOnly:=false,TraceStats:=false,Jobs:=1,JobId:=0)
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    if TodoFile ne "" then
        S := {[StringToInteger(r[1]),StringToInteger(r[2]),StringToInteger(r[3])] where r:=Split(s,":"):s in Split(Read(TodoFile),"\n")};
        L := {r[1]:r in S};
        printf "Loaded todo list with %o items from %o\n", #S, TodoFile;
    else
        S := {};
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
                if #S gt 0 and not [N,k,o] in S then continue; end if;
                n +:= 1;
                if ((n-JobId) mod Jobs) eq 0 then
                    if DimensionsOnly then
                        str := NewspaceData(G,k,o:OrbitRepTable:=T,Detail:=Quiet select 0 else 1);
                    else
                        if not Quiet then printf "Processing space %o:%o:%o with coeffs %o, deg-bound %o\n", N,k,o, Coeffs, DegBound; t:=Cputime(); end if;
                        str := NewspaceData(G,k,o:OrbitRepTable:=T,ComputeTraces,NumberOfCoefficients:=Coeffs,ComputeEigenvalues,ComputeTraceStats:=TraceStats,DegreeBound:=DegBound,Detail:=Quiet select 0 else 1);
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
    n := 0;
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
            if not Quiet then printf "%o:%o:%o:%o\n",r[1],r[2],r[3],r[5]; end if;
        end if;
    end for;
    if not Quiet then printf "Wrote %o records to %\o\n", #S, outfile; end if;
end procedure;

function CompareDataFiles (infile1, infile2:TracesOnly:=false)
    R<x> := PolynomialRing(Rationals());
    fp1 := Open(infile1, "r");
    fp2 := Open(infile2, "r");
    t1 := 0.0; t2:= 0.0;
    n := 1;
    minfields := TracesOnly select 6 else 10;
    while true do
        s1 := Gets(fp1);  s2 := Gets(fp2);
        if IsEof(s1) or IsEof(s2) then break; end if;
        r1 := Split(strip(s1),":"); r2 := Split(strip(s2),":");
        if #r1 lt minfields then printf "Only %o fields in line %o of file %o, expected at least %o!\n", #r1, n, infile1, minfields; print s1; return false; end if;
        if #r2 lt minfields then printf "Only %o fields in line %o of file %o, expected at least %o!\n", #r2, n, infile2, minfields; print s2; return false; end if;
        if r1[1] ne r2[1] then printf "Level %o != %o at line %o\n", r1[1], r2[1], n; return false; end if;
        if r1[2] ne r2[2] then printf "Weight %o != %o at line %o\n", r1[2], r2[2], n; return false; end if;
        if r1[3] ne r2[3] then printf "CharOrbit %o != %o at line %o\n", r1[3], r2[3], n; return false; end if;
        if r1[5] ne r2[5] then printf "Dimensions %o != %o at line %o\n", r1[5], r2[5], n; return false; end if;
        t1 +:= eval(r1[4]); t2 +:= eval(r2[4]);
        if r1[6] ne r2[6] then
            traces1 := eval(r1[6]); traces2 := eval(r2[6]);
            if #traces1 ne #traces2 then printf "Number of trace vectors %o != %o at line %o\n", #traces1, #traces2, n; return false; end if;
            if [#t:t in traces1] ne [#t:t in traces2] then "Number of traces %o != %o at line %o\n", [#t:t in traces1], [#t:t in traces2], n; return false; end if;
            for i:= 1 to #traces1 do
                for j:=1 to #traces1[i] do
                    if traces1[i][j] ne traces2[i][j] then printf "Traces %o != %o disagree for a_%o in trace vector %o at line %o\n", traces1[i][j], traces2[i][j], j, i, n; return false; end if;
                end for;
            end for;
            printf "Wierdness at line %o\n", n; return false;
        end if;
        if TracesOnly then continue; end if;
        if r1[7] ne r2[7] then printf "Atkin-Lehner signs %o != %o at line %o\n", r1[7], r2[7], n; return false; end if;
        if r1[8] ne r2[8] then
            f1 := eval(r1[8]); f2 := eval(r2[8]);
            if #f1 ne #f2 then printf "Different number of field polys at line %o\n", n; return false; end if;
            for i:=1 to #f1 do
                if not NFPolyIsIsomorphic(f1[i],f2[i]) then printf "Coefficient field polys %o != %o do not define the same field at line %o\n", f1[i], f2[i], n; return false; end if;
            end for;
        end if;
        if r1[10] ne r2[10] then
            E1 := eval(r1[10]); E2 := eval(r2[10]);
            if #E1 ne #E2 then printf "Number of eigenvalue vectors %o != %o at line %o\n", #E1, #E2, n; return false; end if;
            for i:=1 to #E1 do
                if not NFPolyIsIsomorphic(E1[i][1],E2[i][1]) then printf "Coefficient field polys %o != %o do not define the same field at line %o\n", E1[i][1], E2[i][1], n; return false; end if;
                C1 := [Eltseq(r) : r in Rows(Matrix(Rationals(),E1[i][5])*Matrix(Rationals(),E1[i][2]))];
                C2 := [Eltseq(r) : r in Rows(Matrix(Rationals(),E2[i][5])*Matrix(Rationals(),E2[i][2]))];
                if #C1 ne #C2 then printf "Different number %o != %o of eigenvalues in entry %o at line %o\n", #C1, #C2, i, n; end if;
                m := Min(#C1,#C2); C1 := [C1[j]:j in [1..m]]; C2 := [C2[j]:j in [1..m]];
                if not NFSeqIsIsomorphic(E1[i][1],C1,E2[i][1],C2) then printf "Eigenvalue mismatch for entry %o at line %o\n", i, n; return false; end if;
            end for;
        end if;
        print n;
        n +:= 1;
    end while;
    printf "Read %o lines from files %o and %o\n", n, infile1, infile2;
    if IsEof(s2) and not IsEof(s1) then printf "Error: reached end of file for %o before %o\n", infile1, infile2; return false; end if;
    if IsEof(s1) and not IsEof(s2) then printf "Error: reached end of file for %o before %o\n", infile1, infile2; return false; end if;
    return true;
end function;
        
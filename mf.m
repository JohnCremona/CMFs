Attach("polredabs.m");
Attach("heigs.m");
load "conrey.m";

// encode Hecke orbit as a 64-bit int
function HeckeOrbitCode (N,k,i,n)
    return N+2^24*k+2^36*i+2^52*n;
end function;

// test whether two irreducible polys define the same field (much faster thatn IsIsomorphic)
function FieldPolysMatch (f,g)
    R<x> := PolynomialRing(Rationals());
    if Type(f) eq SeqEnum then f:=R!f; end if;
    if Type(g) eq SeqEnum then g:=R!g; end if;
    assert IsIrreducible(f) and IsIrreducible(g);
    if Degree(f) ne Degree(g) then return false; end if;
    RR<t>:=PolynomialRing(NumberField(f));
    // if g has a root in Q[x]/(f) then Q[x]/(g) is contained in Q[x]/(f) and we must have equality because degrees match
    return #Roots(RR!Coefficients(g)) gt 0;
end function;

function RestrictChiCodomain (chi)
    N := Modulus(chi); K := Codomain(chi);  QQ := Rationals();
    if K eq QQ then return chi; end if;
    m := Order(chi);
    F := CyclotomicField(m);
    reps := GaloisConjugacyRepresentatives(DirichletGroup(N,F));
    for x in reps do
        m := 2; while Trace(K!Evaluate(x,m)) eq Trace(Evaluate(chi,m)) and m lt N do m +:= 1; end while;
        if m eq N then return x; end if;
    end for;
    print "Unable to restric domain of Dirichlet character!";
    assert false;
end function;
    
function ChiTraces(chi) return [Trace(z):z in ValueList(chi)]; end function;

// Returns Galois orbit reps sorted by order and then lex order on traces of values
function DirichletCharacterReps (N)
    G := [chi:chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N))];
    T := Sort([<[Order(G[i])] cat ChiTraces(G[i]),i>:i in [1..#G]]);
    return [*RestrictChiCodomain(G[T[i][2]]):i in [1..#G]*];
end function;

// This is expensive, only call it once per level
function DirichletCharacterRepTable (G)
    H := FullDirichletGroup(Modulus(G[1]));
    A := AssociativeArray();
    for i:=1 to #G do A[ChiTraces(G[i])]:=i; end for;
    B := AssociativeArray();
    for chi in Elements(H) do B[chi] := A[ChiTraces(RestrictChiCodomain(chi))]; end for;
    return B;
end function;
    
function ConreyLabels (chi)
    N := Modulus(chi);
    v := ChiTraces(chi);
    return [n:n in [1..N]|GCD(n,N) eq 1 and ConreyTraces(N,n) eq v];
end function;

function MinimalConreyLabel (chi)
    n := Min(ConreyLabels(chi));
    return n;
end function;

function DirichletCharacterRepToMinimalConreyLabel (N,i)
    return MinimalConreyLabel (DirichletCharacterReps(N)[i]);
end function;

function ConreyCharacterRep (q, n)
    G := DirichletCharacterReps(q);
    v := ConreyTraces(q,n);
    for i:=1 to #G do
        if v eq ChiTraces(G[i]) then return G[i]; end if;
    end for;
    printf "Unable to match traces for Conrey character q=%o, n=%o\n", q, n;
    assert false;
end function;

function ConreyCharacterRepIndex (q, n)
    G := DirichletCharacterReps(q);
    v := ConreyTraces(q,n);
    for i:=1 to #G do
        if v eq ChiTraces(G[i]) then return i; end if;
    end for;
    printf "Unable to match traces for Conrey character q=%o, n=%o\n", q, n;
    assert false;
end function;

function DirichletCharacterFieldDegree (chi)
    return EulerPhi(Order(chi));
end function;

function SturmBound (N, k)
    return Integers()!Ceiling (Index(Gamma0(N))*k/12);
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
    print "Unable to construct the coefficient field of the form", f;
    assert false;
end function;

function Polredbestify (f)
    for n:=1 to 4 do
        g := f;
        f := Polredbest(g);
        if f eq g then return f; end if;
    end for;
    return f;
end function;

function sum(X) return #X eq 0 select 0 else &+X; end function;

function NewspaceData (G, k, o: DCRepTable:=AssociativeArray(), ComputeTraces:=false, ComputeFields:=false, ComputeCutters:=false, ComputeEigenvalues:=false, NumberOfCoefficients:=0, DegreeBound:=0, EigenvalueDegreeBound:=0, Detail:=false)
    st := Cputime();
    if ComputeEigenvalues then ComputeCutters := true; end if;
    if ComputeCutters then ComputeFields := true; end if;
    if ComputeFields then ComputeTraces := true; end if;
    if EigenvalueDegreeBound gt DegreeBound then DegreeBound := EigenvalueDegreeBound; end if;
    chi := G[o];  N := Modulus(chi);
    if Detail then printf "Decomposing space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
    S := NewformDecomposition(NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1))));
    if Detail then printf "took %o secs\n", Cputime()-t; end if;
    if #S eq 0 then
        if Detail then printf "The space %o:%o:%o is empty\n",N,k,o; end if;
        s := Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-st, []);
        if ComputeTraces then s cat:= ":[]:[]:[]:[]"; end if;
        if ComputeFields then s cat:= ":[]"; end if;
        if ComputeCutters then s cat:= ":[]"; end if;
        if ComputeEigenvalues then s cat:= ":[]"; end if;
        return StripWhiteSpace(s);
    end if;
    d := EulerPhi(Order(chi));
    D := [d*Dimension(S[i]): i in [1..#S]];
    if Detail then printf "dims = %o\n", D; end if;
    // if the dimensions are all distinct then we know that no conjugate spaces were returend by NewformDecomposition
    if not ComputeTraces and not ComputeFields and not ComputeCutters then
        assert sum(D) eq NewspaceDimension(chi,k);
        return StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-st, Sort(D)));
    end if;
    n := Max(2*SturmBound(N,k),NumberOfCoefficients);
    if Detail then printf "Computing %o traces for space %o:%o:%o...", n, N,k,o; t:=Cputime(); end if;
    F := [*Eigenform(S[i],n+1):i in [1..#S]*];
    T := Sort([<[Integers()|Parent(a) eq Rationals() select a else AbsoluteTrace(a) where a:=Coefficient(F[i],j) :j in [1..n]],i>:i in [1..#F]]);
    D := [D[T[i][2]]: i in [1..#T]];  S := [S[T[i][2]]: i in [1..#T]];  F := [*F[T[i][2]]: i in [1.. #T]*];
    T := [T[i][1]:i in [1..#T]];
    if Detail then printf "took %o secs\n", Cputime()-t; printf "Lex sorted traces = %o\n",T; end if;
    if Detail and Order(chi) eq 1 then printf "Computing Atkin-Lehner signs for space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
    AL := Order(chi) eq 1 select [[<p,ExactQuotient(Trace(AtkinLehnerOperator(S[i],p)),D[i])>:p in PrimeDivisors(N)]:i in [1..#S]] else [];
    if Detail and Order(chi) eq 1 then printf "took %o secs.\n", Cputime()-t; printf "Atkin-Lehner signs %o\n", AL; end if;
    if NumberOfCoefficients gt 0 and not &and[#t eq NumberOfCoefficients : t in T] then
        T:=[[T[i][j]:j in [1..NumberOfCoefficients]]: i in [1..#T]];
    end if;
    if NumberOfCoefficients gt 0 then
        if not &and [#v eq NumberOfCoefficients : v in T] then printf "Wrong number of traces for space %o:%o:%o, n=%o, NumberOfCoefficients=%o, [#v : v in T]=%o, T=%o\n",N,k,o, n, NumberOfCoefficients, [#v : v in T], T; assert false; end if;
    else
        assert #Set([#v : v in T]) eq 1;
    end if;
    if Detail then printf "Finding CM forms in space %o:%o:%o...",N,k,o; t:=Cputime(); end if;
    cm := [a select b else 0 where a,b:=IsCM(f:Proof:=true):f in S];
    if Detail then printf "took %o secs\n", Cputime()-t; printf "CM discriminants: %o\n",cm; end if;
    if Detail then printf "Finding inner twists in space %o:%o:%o...",N,k,o; t:=Cputime(); end if;
    if #Keys(DCRepTable) eq 0 then DCRepTable:=DirichletCharacterRepTable(G); end if;
    it := [cm[i] eq 0 select [DCRepTable[t[j]]:j in [2..#t]] where t:= InnerTwists(S[i]:Proof:=true) else [] :i in [1..#S]];
    if Detail then printf "took %o secs\n", Cputime()-t; printf "Inner twists: %o\n",it; end if;
    HF := [];
    if ComputeFields and DegreeBound eq 0 or Min(D) le DegreeBound then
        if Detail then printf "Computing Hecke field polys with degree bound %o for space %o:%o:%o...", DegreeBound,N,k,o; t:=Cputime(); end if;
        HF := [Coefficients(Polredbestify(CoefficientFieldPoly(F[i],D[i]))):i in [1..#D]|DegreeBound eq 0 or D[i] le DegreeBound];
        if Detail then printf "took %o secs\n", Cputime()-t;  printf "Polredbestified Hecke field polys = %o\n", HF; end if;
    end if;
    // TODO: is it really enough to only go up to degree bound
    P:=[[]:d in D|DegreeBound eq 0 or d le DegreeBound];   
    if ComputeCutters and #P gt 0 then
        if Detail then printf "Computing Hecke cutters with degree bound %o for space %o:%o:%o...", DegreeBound,N,k,o; t:=Cputime(); end if;
        p := 2;
        while true do
            if N mod p ne 0 then
                for i:=1 to #P do
                    g := Norm(CharacteristicPolynomial(HeckeOperator(S[i],p)));
                    A := Factorization(g);
                    assert #A eq 1;
                    g := A[1][1]^ExactQuotient(D[i],Degree(A[1][1]));
                    Append(~P[i],<p,Coefficients(g)>);
                end for;
                if #Set(P) eq #P then break; end if;
            end if;
            p := NextPrime(p);
        end while;
        if Detail then printf "took %o secs\n", Cputime()-t; end if;
    end if;
    E := [];
    if ComputeEigenvalues and #[d:d in D|d gt 1 and d le EigenvalueDegreeBound] gt 0 then
        if Detail then printf "Computing exact Hecke eigenvalues with degreebound %o for space %o:%o:%o...", EigenvalueDegreeBound,N,k,o; t:=Cputime(); end if;
        E := [<f,b,n,m select 1 else 0,e> where f,b,n,m,e := ExactHeckeEigenvalues(S[i]): i in [1..#S]|D[i] gt 1 and D[i] le EigenvalueDegreeBound];
        if Detail then printf "took %o secs\n", Cputime()-t; end if;
    end if;
    s := Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-st, D);
    if ComputeTraces then s cat:= Sprintf(":%o:%o:%o:%o",T,cm,it,AL); end if;
    if ComputeFields then s cat:= Sprintf(":%o",HF); end if;
    if ComputeCutters then s cat:= Sprintf(":%o",P); end if;
    if ComputeEigenvalues then s cat:= Sprintf(":%o",E); end if;
    return StripWhiteSpace(s);
end function;

// Decompose spaces S_k(N,chi)^new into Galois stable subspaces for k*N <= B
procedure DecomposeSpaces (filename,B,jobs,jobid:Quiet:=false,Loud:=false,DimensionsOnly:=false,Coeffs:=1000,DegBound:=20,EDegBound:=20)
    n := 0;
    fp := Open(filename,"w");
    for N:=1 to Floor(B/4) do
        if Loud then printf "Constructing CharacterGroup for modulus %o...", N; t:=Cputime(); end if;
        G := DirichletCharacterReps(N);
        T := DirichletCharacterRepTable(G);
        if Loud then printf "took %o secs\n",Cputime()-t; end if;
        for k := 2 to Floor(Sqrt(B/N)) do
            for o in [1..#G] do
                n +:= 1;
                if ((n-jobid) mod jobs) eq 0 then
                    if DimensionsOnly then
                        str := NewspaceData(G,k,o:DCRepTable:=T,Detail:=Loud);
                    else
                        if Loud then printf "Processing space %o:%o:%o with coeffs %o, deg-bound %o, eig-deg-bound %o\n", N,k,o, Coeffs, DegBound,EDegBound; end if;
                        str := NewspaceData(G,k,o:DCRepTable:=T,ComputeEigenvalues,NumberOfCoefficients:=Coeffs,DegreeBound:=DegBound,EigenvalueDegreeBound:=EDegBound,Detail:=Loud);
                    end if;
                    if not Quiet then print str; end if;
                    Puts(fp,str);
                    Flush(fp);
                end if;
            end for;
        end for;
    end for;
end procedure;

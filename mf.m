Attach("polredabs.m");
Attach("chars.m");
Attach("heigs.m");

// test whether two irreducible polys define the same field (much faster than IsIsomorphic)
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
function sprint(X) return StripWhiteSpace(Sprintf("%o",X)); end function;

function NewspaceData (G, k, o: OrbitRepTable:=AssociativeArray(), ComputeTraces:=false, ComputeFields:=false, ComputeCutters:=false, ComputeEigenvalues:=false, NumberOfCoefficients:=0, DegreeBound:=0, Detail:=0)
    st := Cputime();
    if ComputeEigenvalues then ComputeCutters := true; end if;
    if ComputeCutters then ComputeFields := true; end if;
    if ComputeFields then ComputeTraces := true; end if;
    chi := G[o];  N := Modulus(chi);
    if Detail gt 0 then printf "Decomposing space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
    S := NewformDecomposition(NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1))));
    if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
    if #S eq 0 then
        if Detail gt 0 then printf "The space %o:%o:%o is empty\n",N,k,o; end if;
        s := Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-st, []);
        if ComputeTraces then s cat:= ":[]:[]"; end if;
        if ComputeFields then s cat:= ":[]"; end if;
        if ComputeCutters then s cat:= ":[]"; end if;
        if ComputeEigenvalues then s cat:= ":[]:[]:[]:[]"; end if;
        return StripWhiteSpace(s);
    end if;
    d := EulerPhi(Order(chi));
    D := [d*Dimension(S[i]): i in [1..#S]];
    if DegreeBound eq 0 then DegreeBound := Max(D); end if;
    if Detail gt 0 then printf "dims = %o\n", sprint(D); end if;
    // if the dimensions are all distinct then we know that no conjugate spaces were returend by NewformDecomposition
    if not ComputeTraces and not ComputeFields and not ComputeCutters then
        assert sum(D) eq NewspaceDimension(chi,k);
        return StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-st, Sort(D)));
    end if;
    n := Max(HeckeBound(S[1])+20,NumberOfCoefficients);
    if NumberOfCoefficients eq 0 then NumberOfCoefficients := n; end if;
    if Detail gt 0 then printf "Computing %o traces for space %o:%o:%o...", n, N,k,o; t:=Cputime(); end if;
    F := [*Eigenform(S[i],n+1):i in [1..#S]*];
    T := Sort([<[Integers()|Parent(a) eq Rationals() select a else AbsoluteTrace(a) where a:=Coefficient(F[i],j) :j in [1..n]],i>:i in [1..#F]]);
    D := [D[T[i][2]]: i in [1..#T]];  S := [S[T[i][2]]: i in [1..#T]];  F := [*F[T[i][2]]: i in [1.. #T]*];
    T := [T[i][1]:i in [1..#T]];
    if NumberOfCoefficients ne n then T:=[[T[i][j]:j in [1..NumberOfCoefficients]]: i in [1..#T]]; end if;
    if Detail gt 0 then printf "took %o secs\n", Cputime()-t; if Detail gt 1 then printf "Lex sorted traces = %o\n", sprint(T); end if; end if;
    if Detail gt 0 and Order(chi) eq 1 then printf "Computing Atkin-Lehner signs for space %o:%o:%o...", N,k,o; t:=Cputime(); end if;
    AL := Order(chi) eq 1 select [[<p,ExactQuotient(Trace(AtkinLehnerOperator(S[i],p)),D[i])>:p in PrimeDivisors(N)]:i in [1..#S]] else [];
    if Detail gt 0 and Order(chi) eq 1 then printf "took %o secs.\n", Cputime()-t; printf "Atkin-Lehner signs %o\n", sprint(AL); end if;
    HF := [];
    if ComputeFields and not ComputeEigenvalues and Min(D) le DegreeBound then
        if Detail gt 0 then printf "Computing Hecke field polys with degree bound %o for space %o:%o:%o...", DegreeBound,N,k,o; t:=Cputime(); end if;
        HF := [Coefficients(Polredbestify(CoefficientFieldPoly(F[i],D[i]))):i in [1..#D]|DegreeBound eq 0 or D[i] le DegreeBound];
        if Detail gt 0 then printf "took %o secs\n", Cputime()-t;  printf "Polredbestified Hecke field polys = %o\n", HF; end if;
    end if;
    P:=[[]:d in D|d le DegreeBound];   
    if ComputeCutters and #P gt 0 then
        if Detail gt 0 then printf "Computing Hecke cutters with degree bound %o for space %o:%o:%o...", DegreeBound,N,k,o; t:=Cputime(); end if;
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
        if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
    end if;
    E := []; cm := []; it:=[];
    HF := [[0,1]:i in [1..#D]|D[i] eq 1];  pra:=[1:i in [1..#HF]];
    if ComputeEigenvalues then
        if #[d:d in D|d gt 1 and d le DegreeBound] gt 0 then
            if Detail gt 0 then printf "Computing %o exact Hecke eigenvalues with degreebound %o for space %o:%o:%o...", n,DegreeBound,N,k,o; t:=Cputime(); end if;
            E := [<<f,b,n,m select 1 else 0,e>,p select 1 else 0> where f,b,n,m,e,p := ExactHeckeEigenvalues(S[i]:Tnbnd:=n): i in [1..#S]|D[i] gt 1 and D[i] le DegreeBound];
            pra cat:= [e[2]:e in E];
            E := [e[1]:e in E];
            HF cat:= [r[1]:r in E];
            if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;
        end if;
        if Detail gt 0 then printf "Finding CM forms in space %o:%o:%o...",N,k,o; t:=Cputime(); end if;
        cm := [a select b else 0 where a,b:=IsCM(S[i]:Proof:=true):i in [1..#S]|D[i] le DegreeBound];
        if Detail gt 0 then printf "took %o secs\n", Cputime()-t; printf "CM discriminants: %o\n", sprint(cm); end if;
        if Detail gt 0 then printf "Finding inner twists in space %o:%o:%o...",N,k,o; t:=Cputime(); end if;
        if #Keys(OrbitRepTable) eq 0 then _,OrbitRepTable := CharacterOrbitReps (N); end if;
        it := [cm[i] eq 0 select [OrbitRepTable[chi]:chi in t|Order(chi) gt 1] where t:= InnerTwists(S[i]) else [] :i in [1..#S]|D[i] le DegreeBound];
        if Detail gt 0 then printf "took %o secs\n", Cputime()-t; printf "Inner twists: %o\n", sprint(it); end if;
    end if;
    s := Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-st, D);
    if ComputeTraces then s cat:= Sprintf(":%o:%o",T,AL); end if;
    if ComputeFields then s cat:= Sprintf(":%o",HF); end if;
    if ComputeCutters then s cat:= Sprintf(":%o",P); end if;
    if ComputeEigenvalues then s cat:= Sprintf(":%o:%o:%o:%o",E,cm,it,pra); end if;
    return StripWhiteSpace(s);
end function;

// Decompose spaces S_k(N,chi)^new into Galois stable subspaces for k*N <= B
procedure DecomposeSpaces (filename,B,jobs,jobid:Quiet:=false,Loud:=false,DimensionsOnly:=false,Coeffs:=1000,DegBound:=20,TrivialCharOnly:=false)
    st := Cputime();
    n := 0; cnt:=0;
    fp := Open(filename,"w");
    for N:=1 to Floor(B/4) do
        if Loud then printf "Constructing character group data for modulus %o...", N; t:=Cputime(); end if;
        G, T := CharacterOrbitReps(N:RepTable);
        if Loud then printf "took %o secs\n",Cputime()-t; end if;
        for k := 2 to Floor(Sqrt(B/N)) do
            for o in [1..#G] do
                if o gt 1 and TrivialCharOnly then break; end if;
                n +:= 1;
                if ((n-jobid) mod jobs) eq 0 then
                    if DimensionsOnly then
                        str := NewspaceData(G,k,o:OrbitRepTable:=T,Detail:=Loud select 1 else 0);
                    else
                        if Loud then printf "Processing space %o:%o:%o with coeffs %o, deg-bound %o\n", N,k,o, Coeffs, DegBound; end if;
                        str := NewspaceData(G,k,o:OrbitRepTable:=T,ComputeEigenvalues,NumberOfCoefficients:=Coeffs,DegreeBound:=DegBound,Detail:=Loud select 1 else 0);
                    end if;
                    //if not Quiet then print str; end if;
                    Puts(fp,str);
                    Flush(fp);
                    cnt +:= 1;
                end if;
            end for;
        end for;
    end for;
    printf "DecomposeSpaces(\"%o\",%o,%o,%o) succesfully generated %o records using %os of CPU time.\n", filename, B, jobs, jobid, cnt, Cputime()-st;
end procedure;

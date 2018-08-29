Attach("polredabs.m");
Attach("heigs.m");
load "conrey.m";

function HeckeOrbitCode (N,k,i,n)
    return N+2^24*k+2^36*i+2^52*n;
end function;

function RestrictChiCodomain (chi)
    N := Modulus(chi); K := Codomain(chi);  QQ := Rationals();
    if K eq QQ then return chi; end if;
    F := sub<K|ValueList(chi)>;
    if F ne QQ then
        cyc,F := IsCyclotomic(F);
        assert cyc;
    end if;
    reps := GaloisConjugacyRepresentatives(DirichletGroup(N,F));
    for x in reps do
        m := 2; while Trace(K!Evaluate(x,m)) eq Trace(Evaluate(chi,m)) and m lt N do m +:= 1; end while;
        if m eq N then return x; end if;
    end for;
    print "Unable to restric domain of Dirichlet character!";
    assert false;
end function;

// Returns Galois orbit reps sorted by order and then lex order on traces of values
function DirichletCharacterReps (N)
    G := [chi:chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N))];
    T := Sort([<[Order(G[i])] cat [Trace(u):u in ValueList(G[i])],i>:i in [1..#G]]);
    return [*RestrictChiCodomain(G[T[i][2]]):i in [1..#G]*];
end function;

function ConreyLabels (chi)
    N := Modulus(chi);
    v := [Trace(z):z in ValueList(chi)];
    return [n:n in [1..N-1]|GCD(n,N) eq 1 and ConreyTraces(N,n) eq v];
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
        if v eq [Trace(u):u in ValueList(G[i])] then return G[i]; end if;
    end for;
    printf "Unable to match traces for Conrey character q=%o, n=%o\n", q, n;
    assert false;
end function;

function ConreyCharacterRepIndex (q, n)
    G := DirichletCharacterReps(q);
    v := ConreyTraces(q,n);
    for i:=1 to #G do
        if v eq [Trace(u):u in ValueList(G[i])] then return i; end if;
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
    for n:=1 to 10 do
        g := f;
        f := Polredbest(g);
        if f eq g then return f; end if;
    end for;
    return f;
end function;

function sum(X) return #X eq 0 select 0 else &+X; end function;

function NewspaceData (G, k, o: ComputeTraces:=false, ComputeFields:=false, ComputeOperators:=false, ComputeEigenvalues:=false, NumberOfCoefficients:=0, DegreeBound:=0, EigenvalueDegreeBound:=0)
    t := Cputime();
    if ComputeFields then assert ComputeTraces; end if;
    if ComputeOperators then assert ComputeFields; end if;
    if ComputeEigenvalues then assert ComputeOperators; end if;
    chi := G[o];  N := Modulus(chi);
    time S := NewformDecomposition(NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1))));
    if #S eq 0 then
        s := Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-t, []);
        if ComputeTraces then s cat:= ":[]:[]"; end if;
        if ComputeFields then s cat:= ":[]"; end if;
        if ComputeOperators then s cat:= ":[]"; end if;
        if ComputeEigenvalues then s cat:= ":[]"; end if;
        return StripWhiteSpace(s);
    end if;
    d := EulerPhi(Order(chi));
    D := [d*Dimension(S[i]): i in [1..#S]];
    // if the dimensions are all distinct then we know that no conjugate spaces were returend by NewformDecomposition
    if not ComputeTraces and not ComputeFields and not ComputeOperators then
        assert sum(D) eq NewspaceDimension(chi,k);
        return StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o", N, k, o, Cputime()-t, Sort(D)));
    end if;
    n := Max(SturmBound(N,k),NumberOfCoefficients);   // add a fudge factor to prevent Magma dropping trailing zeros
    F := [*Eigenform(S[i],n+1):i in [1..#S]*];
    T := Sort([<[Integers()|Parent(a) eq Rationals() select a else AbsoluteTrace(a) where a:=Coefficient(F[i],j) :j in [1..n]],i>:i in [1..#F]]);
    D := [D[T[i][2]]: i in [1..#T]];  S := [S[T[i][2]]: i in [1..#T]];  F := [*F[T[i][2]]: i in [1.. #T]*];
    T := [T[i][1]:i in [1..#T]];
    AL := Order(chi) eq 1 select [[<p,ExactQuotient(Trace(AtkinLehnerOperator(S[i],p)),D[i])>:p in PrimeDivisors(N)]:i in [1..#S]] else [];
    if NumberOfCoefficients gt 0 and not &and[#t eq NumberOfCoefficients : t in T] then
        T:=[[T[i][j]:j in [1..NumberOfCoefficients]]: i in [1..#T]];
    end if;
    if not &and [#t eq NumberOfCoefficients:t in T] then print Modulus(chi),k,o, [#t:t in T], n, NumberOfCoefficients, T; assert false; end if;
    if ComputeFields then
        F := [Coefficients(Polredbestify(CoefficientFieldPoly(F[i],D[i]))):i in [1..#D]|DegreeBound eq 0 or D[i] le DegreeBound];
    end if;
    if ComputeOperators then
        P:=[[]:d in D|DegreeBound eq 0 or d le DegreeBound];
        N := Modulus(chi);
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
    end if;
    E := [];
    if ComputeEigenvalues and #[d:d in D|d gt 1 and d le EigenvalueDegreeBound] gt 0 then
        E := [<f,b,n,c select 1 else 0,e> where f,b,n,c,e := ExactHeckeEigenvalues(S[i]): i in [1..#S]|D[i] gt 1 and D[i] le EigenvalueDegreeBound];
    end if;
    s := Sprintf("%o:%o:%o:%o:%o", Modulus(chi), k, o, Cputime()-t, D);
    if ComputeTraces then s cat:= Sprintf(":%o:%o",T,AL); end if;
    if ComputeFields then s cat:= Sprintf(":%o",F); end if;
    if ComputeOperators then s cat:= Sprintf(":%o",P); end if;
    if ComputeEigenvalues then s cat:= Sprintf(":%o",E); end if;
    return StripWhiteSpace(s);
end function;

// Decompose spaces S_k(N,chi)^new into Galois stable subspaces for k*N <= B
procedure DecomposeSpaces (filename,B,jobs,jobid:Quiet:=false,DimensionsOnly:=false)
    n := 0;
    fp := Open(filename,"w");
    for N:=1 to Floor(B/2) do
        G:=DirichletCharacterReps(N);
        for k := 2 to Floor(Sqrt(B/N)) do
            for o in [1..#G] do
                n +:= 1;
                if ((n-jobid) mod jobs) eq 0 then
                    if DimensionsOnly then
                        str := NewspaceData(G,k,o);
                    else
                        str := NewspaceData(G,k,o:ComputeTraces,ComputeFields,ComputeOperators,ComputeEigenvalues,NumberOfCoefficients:=100,DegreeBound:=20,EigenvalueDegreeBound:=6);
                    end if;
                    if not Quiet then print str; end if;
                    Puts(fp,str);
                    Flush(fp);
                end if;
            end for;
        end for;
    end for;
end procedure;

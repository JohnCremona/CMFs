function OldDirichletCharacterReps(N)
    G := [chi:chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N))];
    T := Sort([<[Trace(u):u in ValueList(G[i])],i>:i in [1..#G]]);
    return Reverse([G[T[i][2]]:i in [1..#G]]);
end function;

function RestrictChiCodomain (chi)
    N := Modulus(chi); K := Codomain(chi);  QQ := Rationals();
    if K eq QQ then return chi; end if;
    F := sub<K|ValueList(chi)>;
    if F ne QQ then
        cyc,F := IsCyclotomic(sub<K|ValueList(chi)>);
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
function DirichletCharacterReps(N)
    G := [chi:chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N))];
    T := Sort([<[Order(G[i])] cat [Trace(u):u in ValueList(G[i])],i>:i in [1..#G]]);
    return [*RestrictChiCodomain(G[T[i][2]]):i in [1..#G]*];
end function;

function SturmBound (N, k)
    return Integers()!Ceiling (Index(Gamma0(N))*k/12);
end function;

function NewspaceDimension (chi, k)
    return Dimension(NewSubspace(CuspidalSubspace(ModularForms(chi,k))));
end function;

function CoefficientFieldPoly(f,d)
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

function Polredbestify(f)
    while true do
        g := f;
        f := Polredbest(g);
        if f eq g then return f; end if;
    end while;
end function;

function sum(X) return #X eq 0 select 0 else &+X; end function;

function NewspaceData (G, k, o: ComputeTraces:=false, ComputeFields:=false, ComputeOperators:=false, NumberOfCoefficients:=0, DegreeBound:=0)
    t := Cputime();
    if NumberOfCoefficients gt 0 then NumberOfCoefficients +:=1; end if;
    chi := G[o];
    S := NewformDecomposition(NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1))));
    d := EulerPhi(Order(chi));
    D := [d*Dimension(S[i]): i in [1..#S]];
    // if the dimensions are all distinct then we know that no conjugate spaces were returend by NewformDecomposition
    if not ComputeTraces and not ComputeFields and not ComputeOperators then
        assert sum(D) eq NewspaceDimension(chi,k);
        return StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o", Modulus(chi), k, o, Cputime()-t, Sort(D)));
    end if;
    // Initially check for conjugate forms by comparing absolute traces up to the Sturm bound
    // If we hit a trace match we will then check minpolys
    n := Max([SturmBound(Modulus(chi),k),NumberOfCoefficients,10]);
    F := [*Eigenform(S[i],n):i in [1..#S]*];
    T := Sort([<[Integers()|Parent(a) eq Rationals() select a else AbsoluteTrace(a):a in Coefficients(F[i])],i>:i in [1..#F]]);
    D := [D[T[i][2]]: i in [1..#T]];  S := [S[T[i][2]]: i in [1..#T]];  F := [*F[T[i][2]]: i in [1.. #T]*];
    T := [T[i][1]:i in [1..#T]];
    if NumberOfCoefficients gt 0 and n gt NumberOfCoefficients then
        T:=[[T[i][j]:j in [1..NumberOfCoefficients]]: i in [1..#T]];
    end if;
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
    s := Sprintf("%o:%o:%o:%o:%o", Modulus(chi), k, o, Cputime()-t, D);
    if ComputeTraces then s cat:= Sprintf(":%o",T); end if;
    if ComputeFields then s cat:= Sprintf(":%o",F); end if;
    if ComputeOperators then s cat:= Sprintf(":%o",P); end if;
    return StripWhiteSpace(s);
end function;

// Decompose spaces S_k(N,chi)^new into Galois stable subspaces for k*N <= B
procedure DecomposeSpaces(filename,B,jobs,jobid:Quiet:=false,DimensionsOnly:=false)
    n := 0;
    fp := Open(filename,"w");
    for N:=1 to Floor(B/2) do
        G:=DirichletCharacterReps(N);
        for k := 2 to Floor(B/N) do
            for o in [1..#G] do
                n +:= 1;
                if ((n-jobid) mod jobs) eq 0 then
                    if DimensionsOnly then
                        str := NewspaceData(G,k,o);
                    else
                        str := NewspaceData(G,k,o:ComputeTraces,ComputeFields,ComputeOperators,NumberOfCoefficients:=100,DegreeBound:=20);
                    end if;
                    if not Quiet then print str; end if;
                    Puts(fp,str);
                    Flush(fp);
                end if;
            end for;
        end for;
    end for;
end procedure;

// We identify Galois conjugacy classes or Dirichlet characters of modulus N
// by ordinal in reverse lex ordering of traces of values on 1,2,3,..N
function DirichletCharacterGaloisReps(N)
  G := [chi:chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N))];
  T := Sort([<[Trace(u):u in ValueList(G[i])],i>:i in [1..#G]]);
  return Reverse([G[T[i][2]]:i in [1..#G]]);
end function;

function SturmBound (N, k)
    return Integers()!Ceiling (Index(Gamma0(N))*k/12);
end function;

function NewspaceDimension (chi, k)
    return Dimension(NewSubspace(CuspidalSubspace(ModularForms(chi,k))));
end function;

function NewspaceDecomposition (chi, k: ComputeForms:=false, NumberOfCoefficients:=0)
    D := NewformDecomposition(NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1))));
    d := EulerPhi(Order(chi));
    X := [Dimension(D[i]): i in [1..#D]];
    // if the dimensions are all distinct then we know that no conjugate spaces were returend by NewformDecomposition
    if not ComputeForms and #Set(X) eq #X then return Sort([d*x:x in X]); end if;
    // Initially check for conjugate forms by comparing absolute traces up to the Sturm bound
    // If we hit a trace match we will then check minpolys
    n := Max(SturmBound(Modulus(chi),k),NumberOfCoefficients);
    F := [*Eigenform(D[i],n):i in [1..#D]*];
    T := [<[Integers()|a in Integers() select a else Integers()!AbsoluteTrace(a):a in Coefficients(F[i])],i>:i in [1..#D]];
    A := AssociativeArray();
    for r in T do
        A[r[1]] := IsDefined(A,r[1]) select Append(A[r[1]],r[2]) else [r[2]];
        // if we hit two eigenforms with the same traces, verify that they actually have the same minpolys as well
        if #A[r[1]] gt 1 then
            assert [AbsoluteMinimalPolynomial(a):a in Coefficients(F[r[2]])] eq [AbsoluteMinimalPolynomial(a):a in Coefficients(F[A[r[1]][1]])];
        end if;
    end for;
    if ComputeForms then
        X:= Sort([<d*&+[Dimension(D[i]):i in A[r]],A[r][1]>: r in Keys(A)]);
        return [*<r[1],F[r[2]]>:r in X*];
    end if;
    return Sort([d*&+[Dimension(D[i]):i in A[r]] : r in Keys(A)]);
end function;

function CoefficientFieldPolynomial(f,n)
    R<x>:=PolynomialRing(Rationals());
    if n eq 1 then return x; end if;
    a := Coefficients(f);
    assert a[1] eq 1;
    for i:=2 to #a do
        g := AbsoluteMinimalPolynomial(a[i]);
        if Degree(g) eq n then return g; end if;
        assert Degree(g) lt n;
    end for;
    K := NumberField(AbsoluteMinimalPolynomial(a[2]));
    for i:=3 to #a do
        g := AbsoluteMinimalPolynomial(a[i]);
        K := Compositum(K,NumberField(g));
        if Degree(K) eq n then return DefiningPolynomial(K); end if;
        assert Degree(K) lt n;
    end for;
    print "Unable to construct the coefficient field of the form", f;
    assert false;
end function;

function CompareCoefficientVectors(a,b)
    if #a ne #b then return #a-#b; end if;
    if a lt b then return -1; end if;
    if a gt b then return 1; end if;
    return 0;
end function;
    
function NewspaceCoefficientFields (chi, k, DegreeBound)
    X := NewspaceDecomposition (chi, k: ComputeForms:=true, NumberOfCoefficients:=100);
    Y := Sort([Coefficients(Polredbest(CoefficientFieldPolynomial(r[2],r[1]))):r in X|r[1] le DegreeBound],CompareCoefficientVectors);
    return Y;
end function;

function sum(X) return #X eq 0 select 0 else &+X; end function;

// Decompose spaces S_k(N,chi)^new into Galois stable subspaces for k*N <= B
procedure DecomposeSpaces(filename,B,jobs,jobid)
    n := 0;
    S := [Split(r,":"):r in Split(Read(filename),"\n")];
    S := [<eval(a):a in r>:r in S];
    A:=AssociativeArray();
    for r in S do A[<r[1],r[2],r[3]>]:=r; end for;
    fp := Open(filename,"w");
    for N:=1 to Floor(B/2) do
        G:=DirichletCharacterGaloisReps(N);
        for k := 2 to Floor(B/N) do
            for i in [1..#G] do
                n +:= 1;
                if ((n-jobid) mod jobs) eq 0 then
                    if IsDefined(A,<N,k,i>) then
                        t:=A[<N,k,i>][4];
                        X:=A[<N,k,i>][5];
                    else
                        start := Cputime();
                        X:=NewspaceDecomposition(G[i],k);
                        assert sum(X) eq NewspaceDimension(G[i],k);
                        t := Cputime()-start;
                    end if;
                    str:=StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o",N,k,i,t,X));
                    print str;
                    Puts(fp,str);
                    Flush(fp);
                end if;
            end for;
        end for;
    end for;
end procedure;

// Given file containing decompositions of S_k(N,chi)^new into Galois stable subspaces
// compute polredbest field polys (you must Attach(pol"readabs.spec"); before calling
procedure ComputeCoefficientFields(infile,outfile,D,jobs,jobid:B:=0)
    n := 0;
    S := [Split(r,":"):r in Split(Read(infile),"\n")];
    S := [<eval(a):a in r>:r in S];
    fp := Open(outfile,"w");
    oldN := 0;
    for r in S do
        if #r[4] eq 0 or Min(r[4]) gt D then continue; end if;
        if B gt 0 and r[1]*r[2] gt B then continue; end if;
        n +:= 1;
        if ((n-jobid) mod jobs) eq 0 then
            start := Cputime();
            N := r[1]; k:= r[2]; i:=r[3];
            if Max([a:a in r[4]|a le D]) eq 1 then
                // don't bother decomposing the space if all the coefficient fields we care about are equal to Q
                F:=[[0,1]:a in r[4]|a eq 1];
            else
                if N ne oldN then G:=DirichletCharacterGaloisReps(N); oldN := N; end if;
                F := NewspaceCoefficientFields(G[i], k, D);
            end if;
            t := Cputime()-start;
            str := StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o",N,k,i,r[4],F));
            print str, t;
            Puts(fp,str);
            Flush(fp);
        end if;
    end for;
    print n;
end procedure;

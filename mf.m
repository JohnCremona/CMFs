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

function NewspaceDecomposition (chi, k)
    D := NewformDecomposition(NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1))));
    d := EulerPhi(Order(chi));
    X := [Dimension(D[i]): i in [1..#D]];
    // if the dimensions are all distinct then we know that no conjugate spaces were returend by NewformDecomposition
    if #Set(X) eq #X then return Sort([d*x:x in X]); end if;
    // Initially check for conjugate forms by comparing absolute traces up to the Sturm bound
    // If we hit a trace match we will then check minpolys
    n := SturmBound(Modulus(chi),k);
    T:= Sort([<[Integers()|a in Integers() select a else Integers()!AbsoluteTrace(a):a in Coefficients(Eigenform(D[i],n))],i>:i in [1..#D]]);
    A := AssociativeArray();
    for r in T do
        A[r[1]] := IsDefined(A,r[1]) select Append(A[r[1]],r[2]) else [r[2]];
        // if we hit two eigenforms with the same traces, verify that they actually have the same minpolys as well
        if #A[r[1]] gt 1 then
            assert [AbsoluteMinimalPolynomial(a):a in Coefficients(Eigenform(D[r[2]],n))] eq [AbsoluteMinimalPolynomial(a):a in Coefficients(Eigenform(D[A[r[1]][1]],n))];
        end if;
    end for;
    X := [&+[Dimension(D[i]):i in A[r]] : r in Keys(A)];
    return Sort([d*x:x in X]);
end function;

function sum(X) return #X eq 0 select 0 else &+X; end function;

// Decompose spaces S_k(N,chi)^new for k*N <= B
procedure DecomposeSpaces(filename,B,jobs,jobid)
    n := 0;
    fp := Open(filename,"w");
    for N:=1 to Floor(B/2) do
        G:=DirichletCharacterGaloisReps(N);
        for k := 2 to Floor(B/N) do
            for i in [1..#G] do
                n +:= 1;
                if ((n-jobid) mod jobs) eq 0 then
                    start := Cputime();
                    X:=NewspaceDecomposition(G[i],k);
                    assert sum(X) eq NewspaceDimension(G[i],k);
                    t := Cputime()-start;
                    str:=StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o",N,k,i,t,X));
                    print str;
                    Puts(fp,str);
                    Flush(fp);
                end if;
            end for;
        end for;
    end for;
end procedure;

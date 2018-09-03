// Various functions useful for working with Dirichlet characters, their Galois orbits, and Conrey labels

intrinsic Parity (chi::GrpDrchElt) -> RngIntElt
{ The value of the character on -1. }
    return Integers()!Evaluate(chi,-1);
end intrinsic;

intrinsic CharacterFieldDegree (chi::GrpDrchElt) -> RngIntElt
{ The degree of the number field Q(chi). }
    return EulerPhi(Order(chi));
end intrinsic;

intrinsic NumberOfCharacterOrbits (N::RngIntElt) -> RngIntElt
{ The number of Galois orbits of Dirichlet characters of modulus N. }
    // this could be made faster but it is already plenty fast for N up to 10^5
    return Integers()! &+[1/EulerPhi(Order(g)):g in MultiplicativeGroup(Integers(N))];
end intrinsic;

intrinsic CharacterOrbitVector(chi::GrpDrchElt) -> SeqEnum[RngIntElt]
{ The list [Order(chi)] cat [Trace(chi(n)): n in [1..Modulus(chi)] used to sort and uniquely identify Galois orbits of Dirichlet characters. }
    return [Order(chi)] cat [Trace(z):z in ValueList(chi)];
end intrinsic;

intrinsic CharacterOrbitReps(N::RngIntElt:RepTable:=false) -> List, Assoc
{ The list of Galois orbit representatives of the full Dirichlet group of modulus N with minimal codomains sorted by order and trace vectors.
  If the optional boolean argument RepTable is set then a table mapping Dirichlet characters to indexes in this list is also returned. }
    G := [* MinimalBaseRingCharacter(chi): chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N)) *];
    T := Sort([<CharacterOrbitVector(G[i]),i>:i in [1..#G]]);
    if RepTable then
        H := Elements(FullDirichletGroup(N));
        S := Sort([<CharacterOrbitVector(MinimalBaseRingCharacter(H[i])),i>:i in [1..#H]]);
        j := 1;
        A := AssociativeArray(Parent(H[1]));
        for i:=1 to #S do
            while T[j][1] ne S[i][1] do j+:=1; end while;
            A[H[S[i][2]]] := j;
        end for;
        return [* G[T[i][2]] : i in [1..#G] *],A;
    else
        return [* G[T[i][2]] : i in [1..#G] *],_;
    end if;
end intrinsic;

intrinsic ConreyCharacterValue(q::RngIntElt,n::RngIntElt,m::RngIntElt) -> FldCycElt
{ The value of the Dirichlet character with Conry label q.n at the integer m. }
    if q eq 1 then return 1; end if;
    if GCD(q,n) ne 1 or GCD(q,m) ne 1 then return 0; end if;
    if n mod q eq 1 or m mod q eq 1 then return 1; end if;
    b,p,e:= IsPrimePower(q);
    if not b then return &*[$$(a[1]^a[2],n,m):a in Factorization(q)]; end if;
    R := Integers(q);
    k := EulerPhi(q);
    if p gt 2 then
        r := R!PrimitiveRoot(p);
        A := AssociativeArray();
        for i in [1..k] do A[r^i]:=i; end for;
        a := A[R!n]; b:=A[R!m];
        return RootOfUnity(k)^(a*b);
    else
        if e eq 2 then return -1; end if;   // must have n=m=3 since all other cases handled above
        assert e gt 2;
        r := R!5;
        A := AssociativeArray();
        for s in [1,-1], i in [1..k] do A[s*r^i]:=<s,i>; end for;
        a := A[R!n]; b:=A[R!m];
        return RootOfUnity(8)^((1-a[1])*(1-b[1])) * RootOfUnity(2^(e-2))^(a[2]*b[2]);
    end if;
end intrinsic;

intrinsic ConreyCharacterValues(q::RngIntElt,n::RngIntElt,M::RngIntElt) -> SeqEnum[FldCycElt]
{ The list of values of the Dirichlet character with Conrey label q.n on the integers 1..M. }
    if q eq 1 then return [1:i in [1..M]]; end if;
    if GCD(q,n) ne 1 then return [0:i in [1..M]]; end if;
    if n mod q eq 1 then return [GCD(i,q) eq 1 select 1 else 0:i in [1..M]]; end if;
    b,p,e:= IsPrimePower(q);
    if not b then 
        X := [$$(a[1]^a[2],n,M):a in Factorization(q)];
        return [&*[X[i][m]:i in [1..#X]]:m in [1..M]];
    end if;
    R := Integers(q);
    k := EulerPhi(q);
    if p gt 2 then
        r := R!PrimitiveRoot(p);
        A := AssociativeArray();
        for i in [1..k] do A[r^i]:=i; end for;
        a := A[R!n];
        return [GCD(p,m) eq 1 select RootOfUnity(k)^(a*A[R!m]) else 0 : m in [1..M]];
    else
        if e eq 2 then return [IsOdd(m) select (-1)^ExactQuotient(m-1,2) else 0:m in [1..M]]; end if;
        assert e gt 2;
        r := R!5;
        A := AssociativeArray();
        for s in [1,-1], i in [1..k] do A[s*r^i]:=<s,i>; end for;
        a := A[R!n];
        return [GCD(p,m) eq 1 select RootOfUnity(8)^((1-a[1])*(1-b[1])) * RootOfUnity(2^(e-2))^(a[2]*b[2]) where b:=A[R!m] else 0 : m in [1..M]];
    end if;
end intrinsic;

intrinsic ConreyCharacter(q::RngIntElt,n::RngIntElt) -> GrpDrchElt
{ The Dirichlet character with Conrey label q.n. }
    assert GCD(q,n) eq 1;
    G,pi := MultiplicativeGroup(Integers(q));  psi := Inverse(pi);  S := Generators(G);
    m := Order(psi(n));  F := CyclotomicField(m);
    H := Elements(DirichletGroup(q,F));
    v := [F!ConreyCharacterValue(q,n,Integers()!pi(g)):g in S];
    M := [chi: chi in H | Order(chi) eq m and [Evaluate(chi,pi(g)):g in S] eq v];
    assert #M eq 1;
    return M[1];
end intrinsic;

intrinsic ConreyTraces(q::RngIntElt,n::RngIntElt) -> SeqEnum[RngIntElt]
{ The list of traces of values of the Dirichlet character with Conrey label q.n on the integers 1,2,...q. }
    G,pi := MultiplicativeGroup(Integers(q));
    F := CyclotomicField(Order(Inverse(pi)(Integers(q)!n)));
    return [Trace(F!z):z in ConreyCharacterValues(q,n,q)];
end intrinsic;

intrinsic ConreyLabel(chi::GrpDrchElt) -> RngIntElt, RngIntElt
{ The integer n such that q.n is the Conrey label of the specified Dirichlet character of modulus q. }
    q := Modulus(chi);  m := Order(chi);
    G,pi := MultiplicativeGroup(Integers(q));  psi:=Inverse(pi);  S := Generators(G);
    F := CyclotomicField(m);
    v := [F!Evaluate(chi,pi(g)):g in S];
    M := [n : n in [1..q] | GCD(n,q) eq 1 and Order(psi(n)) eq m and [F!ConreyCharacterValue(q,n,Integers()!pi(g)):g in S] eq v];
    assert #M eq 1;
    return M[1];
end intrinsic;

intrinsic ConreyLabels (chi::GrpDrchElt) -> SeqEnum[RngIntElt]
{ The sorted list of integers n giving the Conrey labels q.n of all Galois conjugates of the specified Dirichlet character of modulus q. }
    q := Modulus(chi);  m := Order(chi);
    _,pi := MultiplicativeGroup(Integers(q));  psi:=Inverse(pi);
    v := [Trace(z) : z in ValueList(MinimalBaseRingCharacter(chi))];
    M := [n : n in [1..q] | GCD(n,q) eq 1 and Order(psi(n)) eq m and ConreyTraces(q,n) eq v];
    assert #M gt 0;
    return M;
end intrinsic;

intrinsic MinimalConreyLabel (chi::GrpDrchElt) -> RngIntElt
{ The least positive integer n such that q.n is the Conrey label of the specified Dirichlet character of modulus q. }
    return Min(ConreyLabels(chi));
end intrinsic;

intrinsic ConreyCharacterOrbitIndex (q::RngIntElt,n::RngIntElt) -> RngIntElt
{ The index of representative of the Galois orbit of the Conrey character q.n in the list returned by CharacterOrbitReps(q). }
    _,pi := MultiplicativeGroup(Integers(q)); m := Order(Inverse(pi)(n));
    G := CharacterOrbitReps(q);
    v := ConreyTraces(q,n);
    M := [i:i in [1..#G] | Order(G[i]) eq m and v eq [Trace(z):z in ValueList(G[i])]];
    assert #M eq 1;
    return M[1];
end intrinsic;

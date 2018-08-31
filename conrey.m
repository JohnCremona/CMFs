function ConreyCharacterValue(q,n,m)
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
end function;
    
function ConreyCharacterValues(q,n,M)
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
end function;
    
function ConreyTraces(q,n)
    F:=CyclotomicField(Exponent(MultiplicativeGroup(Integers(q))));
    return [Trace(F!z):z in ConreyCharacterValues(q,n,q)];
end function;

function DirichletCharacterGaloisReps(N)
  G := [chi:chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N))];
  T := Sort([<[Order(G[i])] cat [Trace(u):u in ValueList(G[i])],i>:i in [1..#G]]);
  return [G[T[i][2]]:i in [1..#G]];
end function;

function ConreyLabelOrbits(N)
    G := DirichletCharacterGaloisReps(N);
    A := AssociativeArray();
    for i:=1 to #G do A[[Trace(z):z in ValueList(G[i])]]:=i; end for;
    O := [[]:i in [1..#G]];
    for n:=1 to N-1 do if GCD(N,n) eq 1 then Append(~O[A[ConreyTraces(N,n)]], n); end if; end for;
    return O;
end function;

function ConreyLabels(chi)
    N := Modulus(chi);
    v := [Trace(z):z in ValueList(chi)];
    return [n:n in [1..N-1]|GCD(n,N) eq 1 and ConreyTraces(N,n) eq v];
end function;

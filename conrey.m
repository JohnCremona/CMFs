intrinsic ConreyCharacterValue(q::RngIntElt,n::RngIntElt,m::RngIntElt) -> FldCycElt
{ Compute chi_q(n,m), the value of the Dirichlet character with Conry label q.n at the integer m. }
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
{ Computes [chi_q(n,m):m in [1..M]], the list of values of the Dirichlet character with Conrey label q.n on the integers 1..M. }
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

intrinsic ConreyTraces(q::RngIntElt,n::RngIntElt) -> SeqEnum[RngIntElt]
{ Computes [tr(chi_q(n,m):m in [1..q]], the trace vector of the Dirichlet character with Conrey label q.n. }
    G,pi:=MultiplicativeGroup(Integers(q));
    F:=CyclotomicField(Order(Inverse(pi)(Integers(q)!n)));
    return [Trace(F!z):z in ConreyCharacterValues(q,n,q)];
end intrinsic;

intrinsic ConreyLabel(chi::GrpDrchElt) -> RngIntElt, RngIntElt
{ Painfully slow naive algorithm to compute the Conrey label of a Dirichlet character. }
    q := Modulus(chi);
    v := ValueList(chi);
    for n := 1 to q do
        if ConreyCharacterValues(q,n,q) eq v then return q,n; end if;
    end for;
    error Sprintf("Unable to compute Conrey label of character chi = %o of modulus %o; this should be impossible!", chi, q);
end intrinsic;


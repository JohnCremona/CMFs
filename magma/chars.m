// Various functions useful for working with Dirichlet characters, their Galois orbits, and Conrey labels

// depens on utils.m

intrinsic Parity (chi::GrpDrchElt) -> RngIntElt
{ The value of the character on -1. }
    return Integers()!Evaluate(chi,-1);
end intrinsic;

intrinsic IsReal (chi::GrpDrchElt) -> BoolElt
{ Whether the character takes only real values (trivial or quadratic) or not. }
    return Order(chi) le 2;
end intrinsic;

intrinsic Degree (chi::GrpDrchElt) -> RngIntElt
{ The degree of the number field Q(chi). }
    return EulerPhi(Order(chi));
end intrinsic;

intrinsic UnitGenerators (chi::GrpDrchElt) -> SeqEnum[RngIntElt]
{ Lift to Z of standard generators for (Z/NZ)* where N is the modulus of chi. }
    return UnitGenerators(Parent(chi));
end intrinsic;

intrinsic UnitGenerators (N::RngIntElt) -> SeqEnum[RngIntElt]
{ Lift to Z of standard generators for (Z/NZ)*. }
    return UnitGenerators(DirichletGroup(N));
end intrinsic;

intrinsic UnitGeneratorOrders (N::RngIntElt) -> SeqEnum[RngIntElt]
{ Lift of orders of standard generators for (Z/NZ)*. }
    G,pi:=MultiplicativeGroup(Integers(N));
    return [Order(Inverse(pi)(n)):n in UnitGenerators(N)];
end intrinsic;

intrinsic UnitGeneratorOrders (chi::GrpDrchElt) -> SeqEnum[RngIntElt]
{ List of orders of standard generators for (Z/NZ)* where N is the modulus of chi. }
    return UnitGeneratorOrders(Modulus(chi));
end intrinsic;

intrinsic Factorization (chi::GrpDrchElt) -> List
{ Returns a list of Dirichlet characters of prime power modulus whose product is equal to chi (the empty list if chi has modulus 1). }
    N := Modulus(chi);  F := Codomain(chi);
    if N eq 1 then return [**]; end if;
    Q := [a[1]^a[2]:a in Factorization(N)];
    lift := func<i,n|CRT([j eq i select n else 1 : j in [1..#Q]],Q)>;
    return [* DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(Q[i],F),[chi(lift(i,n)):n in UnitGenerators(Q[i])]) : i in [1..#Q] *];
end intrinsic;

intrinsic Product (chis::List) -> GrpDrchElt
{ Returns the product of the given list of Dirichlet characters (the trivial character for an empty list). }
    if #chis eq 0 then return DirichletGroup(1)!1; end if;
    chi := chis[1]; for i:=2 to #chis do chi *:= chis[i]; end for;
    return chi;
end intrinsic;

intrinsic IsMinimal (chi::GrpDrchElt) -> BoolElt
{ Returns true if the specified Dirichlet character is minimal in the sense of Booker-Lee-Strombergsson (Twist-minimal trace formulas and Selberg eignvalue conjedcture). }
    c := Conductor(chi);
    for chip in Factorization(chi) do
        b,p,e := IsPrimePower(Modulus(chip));  assert b;
        s := Valuation(c,p);
        if p gt 2 then
            if s ne 0 and s ne e and Order(chip) ne 2^Valuation(p-1,2) then return false; end if;
        else
            if s ne e div 2 and s ne e then
                if e le 3 then
                    if s ne 0 then return false; end if;
                else
                    if IsEven(e) then return false; end if;
                    if s ne 0 and s ne 2 then return false; end if;
                end if;
            end if;
        end if;
    end for;
    return true;
end intrinsic;

intrinsic IsMinimalSlow (chi::GrpDrchElt) -> BoolElt
{ Slow version of IsMinimal. }
    b,p,e := IsPrimePower(Modulus(chi));
    if not b then return &and[$$(chip):chip in Factorization(chi)]; end if;
    N := Modulus(chi); c := Conductor(chi);
    if c*c gt N and c ne N then return false; end if;
    if p eq 2 and e gt 3 and IsEven(e) and c lt Sqrt(N) then return false; end if;
    n := Order(chi);
    return #[psi: psi in Elements(FullDirichletGroup(N))|Conductor(psi)*Conductor(psi*chi) le N and (Order(chi*psi^2) lt n or Conductor(chi*psi^2) lt c)] eq 0;
end intrinsic;

intrinsic UnitGeneratorsLogMap (N::RngIntElt, u::SeqEnum[RngIntElt]) -> UserProgram
{ Given a list of generators for (Z/NZ)* returns a function that maps integers coprime to N to a list of exponents writing the input as a power product over the given generators. }
    // We use an O(#(Z/NZ)*) algorithm to compute a discrete log lookup table; for small N this is faster than being clever (but for large N it won't be)
    // Impelemnts Algorithm 2.2 in https://arxiv.org/abs/0903.2785, but we don't bother saving power relations
    if N le 2 then return func<x|[]>; end if;
    ZNZ := Integers(N);  r := [Integers()|];
    n := #u;
    T := [ZNZ!1];
    g := ZNZ!u[1]; h := g; while h ne 1 do Append(~T,h); h *:= g; end while;
    r := [#T];
    for i:=2 to n do
        X := Set(T); S := T; j := 1;
        g := u[i];  h := g; while not h in X do S cat:= [h*t:t in T]; h *:= g; j +:= 1; end while;
        Append(~r,j);  T := S;
    end for;
    ZZ := Integers();
    // Stupid apporach to computing a mapg that given n in [1..N] returns the number of positive integers < n coprime to N
    // (doesn't really matter since we are already spending linear time, but wastes memory and could be eliminated).
    A := [ZZ|0:i in [1..N]];
    for i:=1 to #T do A[ZZ!T[i]] := i-1; end for;
    rr := [ZZ|1] cat [&*r[1..i-1]:i in [2..n]];
    return func<x|[(A[ZZ!x] div rr[i]) mod r[i] : i in [1..n]]>;
end intrinsic;

intrinsic NumberOfCharacterOrbits (N::RngIntElt:OrderBound:=0) -> RngIntElt
{ The number of Galois orbits of Dirichlet characters of modulus N (of order <= OrderBound, if specified). }
    require N gt 0: "Modulus N must be a positive integer";
    // this could be made faster but it is already pretty fast for N up to 10^5
    G := MultiplicativeGroup(Integers(N));
    X := {*Order(g):g in G*};  S := Set(X);  if OrderBound gt 0 then S := {n: n in S| n le OrderBound}; end if;
    return &+[Multiplicity(X,n) div EulerPhi(n):n in S];
end intrinsic;

intrinsic CharacterOrbitLabel (N::RngIntElt,o::RngIntElt) -> MonStgElt
{ Label N.o of the character orbit of modulus N and orbit index i. }
    return Sprintf("%o.%o",N,Base26Encode(o-1));
end intrinsic;

intrinsic CharacterOrbitLabel (label::MonStgElt) -> MonStgElt
{ Returns the character orbit label N.a for the specified Conrey character or character orbit. }
    return CharacterOrbitLabel(DirichletCharacter(label));
end intrinsic;

intrinsic CharacterOrbit (label::MonStgElt) -> RngIntElt
{ Returns the character orbit index for the specified Conrey character or character orbit. }
    return CharacterOrbit(DirichletCharacter(label));
end intrinsic;

intrinsic SplitCharacterLabel (label::MonStgElt) -> RngIntElt, RngIntElt
{ Modulus q and Conrey index n of Conrey character lable q.n, or modulus N and orbit index o of character orbit label N.o (where o is base26 encoded). }
    s := Split(label,".");
    require #s eq 2: "Character labels should be strings of the form q.n (with q and n coprime positive integers) or N.o (with N a positive integer and o a bas26 encoded orbit index)";
    return s[2][1] ge "0" and s[2][1] le "9" select [StringToInteger(s[1]),StringToInteger(s[2])] else [StringToInteger(s[1]),Base26Decode(s[2])+1];
end intrinsic;

intrinsic SplitCharacterOrbitLabel (label::MonStgElt) -> RngIntElt, RngIntElt
{ Modulus N and orbit index o of character orbit label N.o (where o is base26 encoded). }
    s := Split(label,".");
    require #s eq 2: "Character orbit labels should be strings of the form N.o where N is a modulus and o is a bas26 encoded orbit index";
    return [StringToInteger(s[1]),Base26Decode(s[2])+1];
end intrinsic;

intrinsic CompareCharacterOrbitLabels (s::MonStgElt,t::MonStgElt) -> RngIntElt
{ Compares character orbit labels (returns an integer less than, equal to, or greater than 0 indicating the result). }
    return s eq t select 0 else (SplitCharacterOrbitLabel(s) lt SplitCharacterOrbitLabel(t) select -1 else 1);
end intrinsic;

intrinsic CharacterOrbitOrder (N::RngIntElt,n::RngIntElt) -> RngIntElt
{ The order of the characters in the nth orbit of modulus N. }
    require N gt 0 and n gt 0: "Modulus N and orbit index n must be positive integers";
    // this could be made faster but it is already pretty fast for N up to 10^5
    G := MultiplicativeGroup(Integers(N));
    X := {*Order(g):g in G*};  S := Sort({@ o : o in X @});
    m := 0; for i:=1 to #S do m +:= Multiplicity(X,S[i]) div EulerPhi(S[i]); if m ge n then return S[i]; end if; end for;
    require m ge n: Sprintf("Specified n=%o is not a valid orbit index for the specified modulus N=%o (there are only %o orbits)\n", n, N, m);
end intrinsic;

intrinsic CharacterOrbitOrder (label::MonStgElt) -> RngIntElt
{ The order of the characters in the specified character orbit. }
    return CharacterOrbitOrder(x[1],x[2]) where x := SplitCharacterOrbitLabel(label); 
end intrinsic;

intrinsic CharacterOrbitDegree (label::MonStgElt) -> RngIntElt
{ The order of the characters in the specified character orbit. }
    return EulerPhi(CharacterOrbitOrder(label));
end intrinsic;

intrinsic NumberOfTrivialCharacterOrbits (N::RngIntElt) -> RngIntElt
{ The number of trivial Galois orbits of Dirichlet characters of modulus N (number of characters of degree 1). }
    require N gt 0: "Modulus N must be a positive integer";
    w := #PrimeDivisors(N);
    if Valuation(N,2) eq 1 then w -:= 1; end if;
    if Valuation(N,2) gt 2 then w +:= 1; end if;
    return 2^w;
end intrinsic;

intrinsic IsConjugate (chi1::GrpDrchElt,chi2::GrpDrchElt) -> Boolean
{ Returns true if chi1 and chi2 are Galois conjugate Dirichlet characters. }
    e := Order(chi1);
    if Order(chi2) ne e then return false; end if;
    chi1 := MinimalBaseRingCharacter(chi1);  chi2 := MinimalBaseRingCharacter(chi2);
    v1 := ValuesOnUnitGenerators(chi1);  v2 := ValuesOnUnitGenerators(chi2);
    if [OrderOfRootOfUnity(a,e):a in v1] ne [OrderOfRootOfUnity(a,e): a in v2] then return false; end if;
    return #Set(GaloisConjugacyRepresentatives([chi1,Parent(chi1)!chi2])) eq 1 select true else false;
end intrinsic;

intrinsic CompareCharacters (chi1::GrpDrchElt,chi2::GrpDrchElt) -> RngIntElt
{ Compare Dirichlet characters based on order and lexicographic ordering of traces. }
    N := Modulus(chi1);  assert Modulus(chi2) eq N;
    n1 := Order(chi1); n2 := Order(chi2);
    if n1 ne n2 then return n1-n2; end if;
    // this will be very slow when the characters are actually conjugate, try to avoid this use case
    for a:=2 to N-1 do
        if GCD(a,N) ne 1 then continue; end if;
        t1 := Trace(chi1(a));  t2 := Trace(chi2(a));
        if t1 ne t2 then return t1-t2; end if;
    end for;
    return 0;
end intrinsic;

intrinsic CompareConreyCharacters (q::RngIntElt, n1::RngIntElt, n2::RngIntElt) -> RngIntElt
{ Compare two Conrey characters of modulus q based on order and lexicographic ordering of traces. }
    Zq := Integers(q);
    m1 := Order(Zq!n1); m2 := Order(Zq!n2);
    if m1 ne m2 then return m1-m2; end if;
    // this will be very slow when the characters are actually conjugate, try to avoid this use case
    for a:=2 to q-1 do
        if GCD(a,q) ne 1 then continue; end if;
        t1 := Trace(ConreyCharacterValue(q,n1,a));  t2 := Trace(ConreyCharacterValue(q,n2,a));
        if t1 ne t2 then return t1-t2; end if;
    end for;
    return 0;
end intrinsic;

intrinsic CharacterOrbitReps (N::RngIntElt:RepTable:=false,OrderBound:=0) -> List, Assoc
{ The list of Galois orbit representatives of the full Dirichlet group of modulus N with minimal codomains sorted by order and trace vectors.
  If the optional boolean argument RepTable is set then a table mapping Dirichlet characters to indexes in this list is returned as the second return value. }
    require N gt 0: "Modulus N must be a positive integer";
    if OrderBound eq 1 then chi1:=DirichletGroup(N)!1; if RepTable then T:=AssociativeArray(Parent(chi1)); T[chi1]:=1; return [chi1],T; else return [chi1]; end if; end if;
    // The call to MinimalBaseRingCharacter can be very slow when N is large (this makes no sense it should be easy) */
    G := [* MinimalBaseRingCharacter(chi): chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N)) *];
    X := [i:i in [1..#G]];
    X := Sort(X,func<i,j|CompareCharacters(G[i],G[j])>);
    G := OrderBound eq 0 select [* G[i] : i in X *] else [* G[i] : i in X | Order(G[i]) le OrderBound *];
    if not RepTable then return G; end if;
    H := Elements(FullDirichletGroup(N));
    A := AssociativeArray();
    for i:=1 to #G do v:=[OrderOfRootOfUnity(a,Order(G[i])):a in ValuesOnUnitGenerators(G[i])]; if IsDefined(A,v) then Append(~A[v],i); else A[v]:=[i]; end if; end for;
    if OrderBound gt 0 then H := [chi : chi in H | Order(chi) le OrderBound]; end if;
    T := AssociativeArray(Parent(H[1]));
    for h in H do
        v := [OrderOfRootOfUnity(a,Order(h)):a in ValuesOnUnitGenerators(h)];
        m := A[v];
        if #m eq 1 then
            T[h] := m[1];
        else
            for i in m do if IsConjugate(h,G[i]) then T[h]:=i; break; end if; end for;
        end if;
    end for;
    return G, T;
end intrinsic;

intrinsic ConreyCharacterOrbitReps (q::RngIntElt) -> SeqEnum[MonStgElt]
{ The list of minimal index Conrey labels of Galois orbit representatives of the full Dirichlet group sorted by order and trace vectors. }
    if q eq 1 then return ["1.1"]; end if;
    Zq := Integers(q);
    U,pi := UnitGroup(Zq);
    I := [];
    for m in Divisors(Exponent(U)) do
        X := [pi(u):u in U|Order(u) eq m];
        if #X eq EulerPhi(m) then Append(~I,Integers()!Min(X)); continue; end if;
        while #X gt 0 do
            n := Integers()!Min(X);  Append(~I,n);
            v := ConreyCharacterAngles(q,n);
            V := Set(ConjugateAngles(v));
            X := [x : x in X | not ConreyCharacterAngles(q,Integers()!x) in V];
        end while;
    end for;
    s := IntegerToString(q) cat ".";
    return [s cat IntegerToString(n) : n in Sort(I,func<n1,n2|CompareConreyCharacters(q,n1,n2)>)];
end intrinsic;

intrinsic ConreyCharacterOrbitRep (q::RngIntElt, o::RngIntElt) -> MonStgElt
{ The minimal index Conrey label of the specifed Galois orbit. }
    require o gt 0: "The orbit index must be positive";
    if o eq 1 then return [ IntegerToString(q) cat ".1"]; end if;
    Zq := Integers(q);
    U,pi := UnitGroup(Zq);
    I := [];
    s := IntegerToString(q) cat ".";
    for m in Sort(Divisors(Exponent(U))) do
        if #I ge o then return s cat IntegerToString(Sort(I,func<n1,n2|CompareConreyCharacters(q,n1,n2)>)[o]); end if;
        X := [pi(u):u in U|Order(u) eq m];
        if #X eq EulerPhi(m) then Append(~I,Integers()!Min(X)); continue; end if;
        while #X gt 0 do
            n := Integers()!Min(X);  Append(~I,n);
            v := ConreyCharacterAngles(q,n);
            V := Set(ConjugateAngles(v));
            X := [x : x in X | not ConreyCharacterAngles(q,Integers()!x) in V];
        end while;
    end for;
    assert #I gt 0;
    return s cat IntegerToString(Sort(I,func<n1,n2|CompareConreyCharacters(q,n1,n2)>)[o]);
end intrinsic;

intrinsic ConreyCharacterOrbitRep (s::MonStgElt) -> MonStgElt
{ The minimal index Conrey label of the specifed Galois orbit. }
    a := SplitCharacterOrbitLabel(s);
    return ConreyCharacterOrbitRep(a[1],a[2]);
end intrinsic;


intrinsic CharacterOrbitLabel (chi::GrpDrchElt) -> MonStgElt
{ Label N.o of the orbit of the specified Dirichlet character. }
    return Sprintf("%o.%o",Modulus(chi),Base26Encode(CharacterOrbit(chi)-1));
end intrinsic;

intrinsic CharacterOrbitRep (N::RngIntElt,o::RngIntElt) -> GrpDrchElt
{ Representative element of the orbit with index o of Dirichlet characters of modulus N. }
    require N gt 0 and o gt 0: "Modulus N and orbit index o must be positive integers";
    if o eq 1 then return DirichletGroup(N)!1; end if;
    return DirichletCharacter(ConreyCharacterOrbitRep(N,o));
end intrinsic;

intrinsic CharacterOrbitRep (label::MonStgElt) -> GrpDrchElt
{ Representative element for the Dirichlet character oribt indentified by the label. }
    return CharacterOrbitRep(StringToInteger(x[1]),StringToInteger(x[2])) where x := SplitCharacterOrbitLabel(label);
end intrinsic;

intrinsic CharacterOrbit (chi::GrpDrchElt) -> RngIntElt
{ The index of the orbit of the specified Dirichlet character in the list of orbit representatives returned by CharacterOrbitReps (this can also be determined using the RepTable parameter). }
    m := Order(chi);
    if m eq 1 then return 1; end if;
    if IsCyclic(MultiplicativeGroup(Integers(Modulus(chi)))) then return Index(Divisors(EulerPhi(Modulus(chi))),m); end if;
    v := [Trace(z):z in ValueList(MinimalBaseRingCharacter(chi))];
    G := CharacterOrbitReps(Modulus(chi));
    M := [i : i in [1..#G] | Order(G[i]) eq m and [Trace(z):z in ValueList(G[i])] eq v];
    assert #M eq 1;
    return M[1];
end intrinsic;

intrinsic KroneckerDiscriminant (chi::GrpDrchElt) -> RngIntElt
{ Returns the discriminant of the Kronecker symbold corresponding to the specified character, or zero if none exists (1 for trivial character). }
    if Order(chi) gt 2 then return 0; end if;
    if Order(chi) eq 1 then return 1; end if;
    D := Parity(chi)*Conductor(chi);
    return D mod 4 in [0,1] select D else 0;
end intrinsic;

intrinsic KroneckerCharacterOrbits (M::RngIntElt) -> RngIntElt
{ A list of paris <D,i> where D is a fundamental discriminant dividing the modulus M and i is the orbit index of the corresponding Kronecker character. }
    require M gt 0: "The modulus M should be a positive integer.";
    D := [-d:d in Divisors(M)|IsFundamentalDiscriminant(-d)] cat [d:d in Divisors(M)|IsFundamentalDiscriminant(d)];
    if #D eq 0 then return []; end if;
    if #D eq 1 then return [<D[1],2>]; end if;
    G := DirichletGroup(M);
    X := [G|KroneckerCharacter(d):d in D];
    B := 32;
    while true do T := [[X[i](n):n in [1..B]]:i in [1..#X]]; if #Set(T) eq #T then break; end if; B *:=2; end while;
    X := Sort([<T[i],D[i]>:i in [1..#D]]);
    return [<X[i][2],1+i>:i in [1..#X]];
end intrinsic;

intrinsic KroneckerCharacterOrbit (D::RngIntElt,M::RngIntElt) -> RngIntElt
{ The index of the orbit of the Kronecker character for the fundamental discriminant D in modulus M. }
    require IsFundamentalDiscriminant(D): "D should be a fundamental quadratic discriminant.";
    require M gt 0 and IsDivisibleBy(M,D): "The modulus M should be a positive integer divisible by the fundamental discriminant D.";
    return [r[2] : r in KroneckerCharacterOrbits(M) | r[1] eq D][1];
end intrinsic;

function dlog(p,e,a,b)   // assumes a has order p^e in Integers(p^n) (for some n > e)
    if e eq 0 then assert a eq 1 and b eq 1; return 0; end if;
    if e eq 1 then x:=0; aa := Parent(a)!1; while x lt p do if b eq aa then return x; end if; aa *:= a; x +:= 1; end while; assert false; end if; // TODO: BSGS
    e1 := e div 2; e0 := e-e1;
    x0 := $$(p,e0,a^(p^e1),b^(p^e1));
    x1 := $$(p,e1,a^(p^e0),b*a^(-x0));
    return (x0 + p^e0*x1);
end function;

intrinsic DiscreteLogModEvenPrimePower (e::RngIntElt,n::RngIntElt) -> RngIntElt, RngIntElt
{ Given an exponent e > 2 and an odd integer n returns unique integers a,s such that n = s*5^a mod 2^e with s in [-1,1] and a in [0..e-1]. }
    require e gt 2 and IsOdd(n): "e must be at least 3 and n must be an odd integers";
    R := Integers(2^e);
    s := n mod 4 eq 1 select 1 else -1;
    x := R!s*n;
    a := dlog(2,e-2,R!5,x);
    assert s*(R!5)^a eq R!n;
    return a,s;
end intrinsic;

intrinsic ConreyGenerator (p::RngIntElt) -> RngIntElt
{ For an odd prime p, the least positive integer a that generates (Z/p^eZ)^times for all e. }
    require IsOdd(p): "p must be an odd prime";
    r := PrimitiveRoot(p^2);
    require r gt 0: "p must be an odd prime";
    return r;
end intrinsic;

intrinsic DiscreteLogModOddPrimePower (p::RngIntElt,e::RngIntElt,n::RngIntElt) -> RngIntElt, RngIntElt
{ Given n coprime to the odd prime p returns the integer x in [0..phi(p^e)-1] for which n = r^x mod p^e, where r is the Conrey generator for p. }
    require IsOdd(p) and GCD(p,n) eq 1: "p must be an odd prime and n must not be divisible by p";
    r := ConreyGenerator(p);
    if e eq 1 then return Log(GF(p)!r,GF(p)!n); end if;
    R := Integers(p^e);  pp := p^(e-1);
    x1 := dlog(p,e-1,(R!r)^(p-1),(R!n)^(p-1));
    x2 := Log(GF(p)!(R!r)^pp,GF(p)!(R!n)^pp);
    return CRT([x1,x2],[pp,p-1]);
end intrinsic;

intrinsic ConreyCharacterValue (q::RngIntElt,n::RngIntElt,m::RngIntElt) -> FldCycElt
{ The value chi_q(n,m) of the Dirichlet character with Conry label q.n at the integer m. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if GCD(q,m) ne 1 then return 0; end if;
    if q eq 1 or n mod q eq 1 or m mod q eq 1 then return 1; end if;
    F := CyclotomicField(Order(Integers(q)!n));
    b,p,e:= IsPrimePower(q);
    if not b then return F!&*[$$(a[1]^a[2],n,m):a in Factorization(q)]; end if;
    if p gt 2 then
        a := DiscreteLogModOddPrimePower(p,e,n);  b := DiscreteLogModOddPrimePower(p,e,m); d := (p-1)*p^(e-1);
        return F!(RootOfUnity(d)^(a*b));
    else
        if e eq 2 then assert n mod q eq 3 and m mod q eq 3; return -1; end if; assert e gt 2;
        a,ea := DiscreteLogModEvenPrimePower(e,n);  b,eb := DiscreteLogModEvenPrimePower(e,m); d:= 2^(e-2);
        return F!(RootOfUnity(8)^((1-ea)*(1-eb)) * RootOfUnity(d)^(a*b));
    end if;
end intrinsic;

intrinsic ConreyCharacterValues (q::RngIntElt,n::RngIntElt,S::SeqEnum[RngIntElt]) -> SeqEnum[FldCycElt]
{ The list of values of the Dirichlet character with Conrey label q.n on the integers in S. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if q eq 1 then return [1:i in S]; end if;
    if n mod q eq 1 then return [GCD(q,m) eq 1 select 1 else 0 : m in S]; end if;
    b,p,e:= IsPrimePower(q);
    if not b then 
        X := [$$(a[1]^a[2],n,S):a in Factorization(q)];
        return [&*[X[i][j]:i in [1..#X]] : j in [1..#S]];
    end if;
    if p gt 2 then
        a := DiscreteLogModOddPrimePower(p,e,n);  d := (p-1)*p^(e-1);
        return [GCD(p,m) eq 1 select RootOfUnity(d)^(a*DiscreteLogModOddPrimePower(p,e,m)) else 0 : m in S];
    else
        if e eq 2 then assert n mod q eq 3; return [IsOdd(m) select (-1)^ExactQuotient(m-1,2) else 0 : m in S]; end if;  assert e gt 2;
        a,ea := DiscreteLogModEvenPrimePower(e,n);  d := 2^(e-2);
        return [GCD(p,m) eq 1 select RootOfUnity(8)^((1-ea)*(1-eb)) * RootOfUnity(d)^(a*b) where  b,eb := DiscreteLogModEvenPrimePower(e,m) else 0 : m in S];
    end if;
end intrinsic;

intrinsic ConreyCharacterValues (q::RngIntElt,n::RngIntElt) -> SeqEnum[FldCycElt]
{ The list of values of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    return ConreyCharacterValues(q,n,UnitGenerators(q));
end intrinsic;

intrinsic CharacterValues( q::RngIntElt,n::RngIntElt) -> SeqEnum[FldCycElt]
{ The list of values of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    return ConreyCharacterValues(q,n);
end intrinsic;

intrinsic CharacterValues (chi::GrpDrchElt) -> SeqEnum[FldCycElt]
{ The list of values of the specifed Dirichlet character of modulus N on standard generators for (Z/NZ)* (as returned by UnitGenerators(N)). }
    return [chi(u):u in UnitGenerators(Modulus(chi))];
end intrinsic;

intrinsic NormalizedAngle (r::FldRatElt) -> FldRatElt
{ Given a rational number r return unique positive rational number s <= 1such that s-r is an integer. }
    b:=Denominator(r); a:=Numerator(r) mod b;
    return a eq 0 select Rationals()!1 else a/b;
end intrinsic;

intrinsic ConjugateAngles (v::SeqEnum[FldRatElt]) -> SeqEnum[FldRatElt]
{ Given a list of angles v returns the (normalized) orbit of v under the action of (Z/phi(N)Z)* where N is the LCM of the denominators of v. }
    if #v eq 0 then return v; end if;
    G,pi:=MultiplicativeGroup(Integers(LCM([Denominator(r):r in v])));
    return [[NormalizedAngle((Integers()!pi(g))*r):r in v]:g in G];
end intrinsic;

intrinsic CharacterAngles (chi::GrpDrchElt, S::SeqEnum[RngIntElt]) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the specifed Dirichlet character of modulus N on standard generators for (Z/NZ)* (as returned by UnitGenerators(N)). }
    N := Modulus(chi); m := Order(chi); z := RootOfUnity(m,Codomain(chi));
    return [Rationals()|Min([i:i in [1..m]|z^i eq v])/m where v:=chi(u): u in S];
end intrinsic;

intrinsic CharacterAngles (chi::GrpDrchElt) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the specifed Dirichlet character of modulus N on standard generators for (Z/NZ)* (as returned by UnitGenerators(N)). }
    return CharacterAngles(chi,UnitGenerators(Modulus(chi)));
end intrinsic;

intrinsic ConreyCharacterAngle (q::RngIntElt,n::RngIntElt,m::RngIntElt) -> FldRatElt
{ The rational number r such that chi_q(n,m) = e(r) or 0 if m is not coprime to q. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if GCD(q,m) ne 1 then return Rationals()!0; end if;
    if q eq 1 or n mod q eq 1 or m mod q eq 1 then return Rationals()!1; end if;
    b,p,e:= IsPrimePower(q);
    if not b then return NormalizedAngle(&+[Rationals()|$$(a[1]^a[2],n,m):a in Factorization(q)]); end if;
    if p gt 2 then
        a := DiscreteLogModOddPrimePower(p,e,n);  b := DiscreteLogModOddPrimePower(p,e,m); d := (p-1)*p^(e-1);
        return NormalizedAngle((a*b) / d);
    else
        if e eq 2 then assert n mod q eq 3 and m mod q eq 3; return 1/2; end if; assert e gt 2;
        a,ea := DiscreteLogModEvenPrimePower(e,n);  b,eb := DiscreteLogModEvenPrimePower(e,m); d:= 2^(e-2);
        return NormalizedAngle(((1-ea)*(1-eb)) / 8 + (a*b) / d);
    end if;
end intrinsic;

intrinsic ConreyCharacterComplexValue (q::RngIntElt,n::RngIntElt,m::RngIntElt,CC::FldCom) -> FldComElt
{ Value of chi_q(m,n) in specified complex field. }
    return Exp(2*Pi(CC)*CC.1*ConreyCharacterAngle(q,n,m));
end intrinsic;

intrinsic ConreyCharacterAngles (q::RngIntElt,n::RngIntElt,S::SeqEnum[RngIntElt]) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on the integers m in S (or 0 for m in S not coprime to Q). }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if q eq 1 then return [Rationals()|1:i in S]; end if;
    if n mod q eq 1 then return [Rationals()|GCD(i,q) eq 1 select 1 else 0 : i in S]; end if;
    b,p,e:= IsPrimePower(q);
    if not b then 
        X := [$$(a[1]^a[2],n,S):a in Factorization(q)];
        return [Rationals()|GCD(S[j],q) eq 1 select NormalizedAngle(&+[X[i][j]:i in [1..#X]]) else 0 : j in [1..#S]];
    end if;
    R := Integers(q);
    if p gt 2 then
        a := DiscreteLogModOddPrimePower(p,e,n);  d := (p-1)*p^(e-1);
        return [Rationals()|GCD(m,p) eq 1 select NormalizedAngle((a*b)/d) where b := DiscreteLogModOddPrimePower(p,e,m) else 0 : m in S];
    else
        if e eq 2 then assert n mod q eq 3; return [Rationals()|IsOdd(m) select (IsEven(ExactQuotient(m-1,2)) select 1 else 1/2) else 0 : m in S]; end if; assert e gt 2;
        a,ea := DiscreteLogModEvenPrimePower(e,n);  d:= 2^(e-2);
        return [Rationals()|GCD(m,p) eq 1 select NormalizedAngle(((1-ea)*(1-eb)) / 8 + (a*b) / d) where b,eb := DiscreteLogModEvenPrimePower(e,m) else 0 : m in S];
    end if;
end intrinsic;

intrinsic ConreyCharacterAngles (q::RngIntElt,n::RngIntElt) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    return ConreyCharacterAngles(q,n,UnitGenerators(q));
end intrinsic;

intrinsic ConreyCharacterAngles (s:MonStgEt) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return ConreyCharacterAngles(StringToInteger(t[1]),StringToInteger(t[2]));
end intrinsic;

intrinsic CharacterAngles (q::RngIntElt,n::RngIntElt) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    return ConreyCharacterAngles(q,n,UnitGenerators(q));
end intrinsic;

intrinsic CharacterAngles (s:MonStgEt) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return ConreyCharacterAngles(StringToInteger(t[1]),StringToInteger(t[2]));
end intrinsic;

intrinsic ConreyCharacterComplexValues (q::RngIntElt,n::RngIntElt,S::SeqEnum[RngIntElt],CC::FldCom) -> SeqEnum[FldComElt]
{ List of values of chi_q(n,m) for m in S in specified complex field. }
    return [Exp(2*Pi(CC)*CC.1*t): t in ConreyCharacterAngles(q,n,S)];
end intrinsic;

intrinsic ComplexConreyCharacter (q::RngIntElt,n::RngIntElt,CC::FldCom) -> Map
{ The Dirichlet character with Conrey label q.n with values in the specified complex field. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    chi := CyclotomicConreyCharacter(q,n);
    F := Codomain(chi);
    phi := Degree(F) gt 1 select hom<F->CC|Conjugates(F.1:Precision:=Precision(CC))[1]> else hom<F->CC|>;
    xi := map<Integers()->CC|n:->phi(chi(n))>;
    U := UnitGenerators(chi);
    V := ConreyCharacterComplexValues(q,n,U,CC);
    assert &and[Abs(xi(U[i])-V[i]) lt 10.0^-(Precision(CC) div 2):i in [1..#U]];
    return xi;
end intrinsic;

intrinsic ComplexConreyCharacter (s::MonStgElt,CC::FldCom) -> Map
{ The Dirichlet character with Conrey label q.n. with values in the specific complex field. }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    q := atoi(t[1]); n:= atoi(t[2]);
    return ComplexConreyCharacter(q,n,CC);
end intrinsic;

intrinsic ConreyTraces (q::RngIntElt,n::RngIntElt) -> SeqEnum[RngIntElt]
{ The list of traces of values of the Dirichlet character with Conrey label q.n on the integers 1,2,...q. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    G,pi := MultiplicativeGroup(Integers(q));
    F := CyclotomicField(Order(Inverse(pi)(Integers(q)!n)));
    return [Trace(F!z):z in ConreyCharacterValues(q,n,[1..q])];
end intrinsic;

intrinsic ConreyIndex (chi::GrpDrchElt) -> RngIntElt
{ The integer n such that q.n is the Conrey label of the specified Dirichlet character of modulus q. }
    q := Modulus(chi);  m := Order(chi);
    G,pi := MultiplicativeGroup(Integers(q));  psi:=Inverse(pi);
    v := CharacterAngles(chi);
    M := [n : n in [1..q] | GCD(q,n) eq 1 and Order(psi(n)) eq m and ConreyCharacterAngles(q,n) eq v];
    assert #M eq 1;
    return M[1];
end intrinsic;

intrinsic ConreyLabel (chi::GrpDrchElt) -> MonStgElt
{ Conrey label q.n of the specified Dirichlet character (as a string). }
    return Sprintf("%o.%o",Modulus(chi),ConreyIndex(chi));
end intrinsic;

intrinsic ConreyLabel (N::RngIntElt,o::RngIntElt:OrbitTable:=[]) -> MonStgElt
{ Conrey label of our standard representative of the specifeid Galois orbit of Dirichlet characters of modulus N (which is typically *not* the minimal Conrey label in the orbit). }
    return #OrbitTable ge o select ConreyLabel(OrbitTable[o]) else ConreyLabel(CharacterOrbitRep(N,o));
end intrinsic;

intrinsic ConreyCharacterOrbitIndex (q::RngIntElt,n::RngIntElt) -> RngIntElt
{ The index of representative of the Galois orbit of the Conrey character q.n in the list returned by CharacterOrbitReps(q). }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    _,pi := MultiplicativeGroup(Integers(q)); m := Order(Inverse(pi)(n));
    G := CharacterOrbitReps(q);
    v := ConreyTraces(q,n);
    M := [i:i in [1..#G] | Order(G[i]) eq m and v eq [Trace(z):z in ValueList(G[i])]];
    assert #M eq 1;
    return M[1];
end intrinsic;

intrinsic ConreyCharacterOrbitIndex (s::MonStgElt) -> RngIntElt
{ The index of representative of the Galois orbit of the Conrey character with label s in the list returned by CharacterOrbitReps(q). }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return ConreyCharacterOrbitIndex (t[1],t[2]);
end intrinsic;

intrinsic Order (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The order of the Conrey character q.n. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    return q lt 3 select 1 else Order(Integers(q)!n);
end intrinsic;

intrinsic Order (s::MonStgElt) -> RngIntElt
{ The order of the Conrey character q.n or character orbit label q.a. }
    t := Split(s,".");
    if t[2][1] ge "0" and t[2][1] le "9" then return  Order(StringToInteger(t[1]),StringToInteger(t[2])); end if;
    require t[2][1] ge "a" and t[2][1] le "z":"Label should be either a Conrey label like 7.6 or a charcter orbit label like 7.b.";
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return CharacterOrbitOrder(s);
end intrinsic;

intrinsic Degree (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The degree of the number field generated by the values of the specified Conrey character. }
    return EulerPhi(Order(q,n));
end intrinsic;

intrinsic Degree (s::MonStgElt) -> RngIntElt
{ The degree of the number field generated by the values of the specified Conrey character. }
    return EulerPhi(Order(s));
end intrinsic;

intrinsic IsReal (q::RngIntElt, n::RngIntElt) -> BoolElt
{ Whether the specifed Conrey character takes only real values (trivial or quadratic) or not. }
    return Order(q,n) le 2;
end intrinsic;

intrinsic IsReal (s::MonStgElt) -> BoolElt
{ Whether the specifed Conrey character takes only real values (trivial or quadratic) or not. }
    return Order(s) le 2;
end intrinsic;

intrinsic IsMinimal (q::RngIntElt, n::RngIntElt) -> BoolElt
{ Returns true if the specified Conrey character q.n is minimal in the sense of Booker-Lee-Strombergsson (Twist-minimal trace formulas and Selberg eignvalue conjedcture). }
    c := Conductor(q,n);
    for pp in Factorization(q) do
        p := pp[1]; e:= pp[2]; qp := p^e;
        s := Valuation(c,p);
        if p gt 2 then
            if s ne 0 and s ne e and Order(qp, n mod qp) ne 2^Valuation(p-1,2) then return false; end if;
        else
            if s ne e div 2 and s ne e then
                if e le 3 then
                    if s ne 0 then return false; end if;
                else
                    if IsEven(e) then return false; end if;
                    if s ne 0 and s ne 2 then return false; end if;
                end if;
            end if;
        end if;
    end for;
    return true;
end intrinsic;

intrinsic IsMinimal (s::MonStgElt) -> BoolElt
{ Returns true if the specified Conrey character q.n is minimal in the sense of Booker-Lee-Strombergsson (Twist-minimal trace formulas and Selberg eignvalue conjedcture). }
    t := Split(s,".");
    require #t eq 2: "Label should be either a Conrey label like 7.6 or a charcter orbit label like 7.b.";
    if t[2][1] ge "0" and t[2][1] le "9" then return IsMinimal(StringToInteger(t[1]),StringToInteger(t[2])); end if;
    return IsMinimal(DirichletCharacter(s));
end intrinsic;

intrinsic Factorization (q::RngIntElt, n::RngIntElt) -> SeqEnum
{ Returns the factorization of the Conrey character q.n into Conrey characters q_i.n_i of prime power moduli q_i as a list of pairs of integers [q_i,n_i]. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    return [[qi,n mod qi] where qi:=a[1]^a[2]:a in Factorization(q)];
end intrinsic;

intrinsic Factorization (s::MonStgElt) -> SeqEnum
{ Returns the factorization of the Conrey character q.n into Conrey characters q_i.n_i of prime power moduli q_i as a list of Conrey labels q_i.n_i. }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return [Sprintf("%o.%o",x[1],x[2]):x in Factorization(StringToInteger(t[1]),StringToInteger(t[2]))];
end intrinsic;

intrinsic Parity (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The parity of the Conrey character q.n. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    return &*[Integers()|IsSquare(Integers(p)!n) select 1 else -1 : p in PrimeDivisors(q)] * (IsDivisibleBy(q,4) select (n mod 4 eq 1 select 1 else -1) else 1);
end intrinsic;

intrinsic Parity (s::MonStgElt) -> RngIntElt
{ The parity of the Conrey character q.n. }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return Parity(StringToInteger(t[1]),StringToInteger(t[2]));
end intrinsic;

intrinsic Conductor (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The conductor of the Conrey character q.n. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    c := &*[Integers()|n mod pp eq 1 select 1 else p^(Valuation(Order(Integers(pp)!n),p)+1) where pp:=p^qq[2] where p:=qq[1]:qq in Factorization(q)];
    return c * (e gt 2 and ConreyCharacterValue(2^e,n,5) ne 1 select 2 else 1) where e:=Valuation(q,2);
end intrinsic;

intrinsic Conductor (s::MonStgElt) -> RngIntElt
{ The conductor of the Conrey character q.n. }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return Conductor(StringToInteger(t[1]),StringToInteger(t[2]));
end intrinsic;

intrinsic Modulus (s::MonStgElt) -> RngIntElt
{ The modulus q of the Conrey character q.n. }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return StringToInteger(t[1]);
end intrinsic;

intrinsic IsPrimitive (q::RngIntElt, n::RngIntElt) -> BoolElt
{ Whether the specifed Conrey character q.n is primitive (conductor = modulus = q) or not. }
    return q eq Conductor(q,n);
end intrinsic;

intrinsic IsPrimitive (s::MonStgElt) -> BoolElt
{ Whether the specifed Conrey character q.n is primitive (conductor = modulus = q) or not. }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return IsPrimitive(StringToInteger(t[1]),StringToInteger(t[2]));
end intrinsic;

intrinsic AssociatedCharacter (m::RngIntElt,chi::GrpDrchElt) -> GrpDrchElt
{ The Dirichlet character of modulus m induced by the primitive character inducing chi (whose conductor must divide m). }
    return MinimalBaseRingCharacter(FullDirichletGroup(m)!chi);
end intrinsic;

intrinsic AssociatedCharacter (qq::RngIntElt,q::RngIntElt,n::RngIntElt) -> RngIntElt
{ The Conrey index nn of the Conrey character qq.nn of modulus qq induced by the primitive character inducing the Conrey character q.n. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if q eq 1 or n mod q eq 1 then return 1; end if;
    if qq eq q then return n mod qq; end if;
    b,p,e := IsPrimePower(q);
    if not b then return Integers()!&*[Integers(qq)|$$(qq,r[1],r[2]):r in Factorization(q,n)]; end if;
    ee := Valuation(qq,p); qqp := p^ee; qqnp := qq div qqp;
    if ee eq e then return CRT([n,1],[qqp,qqnp]); end if;
    if IsOdd(p) then
        a := DiscreteLogModOddPrimePower(p,e,n);
        require ee ge e or IsDivisibleBy(a,p^(e-ee)): "Target modulus must be divisible by conductor";
        if ee gt e then a *:= p^(ee-e); else a div:= p^(e-ee); end if;
        return CRT([Integers()!(Integers(qqp)!ConreyGenerator(p))^a,1],[qqp,qqnp]);
    else
        if e eq 2 then assert n eq 3; require ee ge e: "Target modulus must be divisible by conductor"; return CRT([qqp-1,1],[qqp,qqnp]); end if;
        assert e gt 2;
        a,s := DiscreteLogModEvenPrimePower(e,n);
        require ee ge e or IsDivisibleBy(a,2^(e-ee)): "Target modulus must be divisible by conductor";
        if ee gt e then a *:= 2^(ee-e); else a div:= 2^(e-ee); end if;
        return CRT([Integers()!(s*(Integers(qqp)!5)^a),1],[qqp,qqnp]);
    end if;
end intrinsic;

intrinsic AssociatedCharacter (qq::RngIntElt,s::MonStgElt) -> MonStgElt
{ Conrey character qq.nn of modulus qq induced by the primitive character inducing the Conrey character q.n. }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return Sprintf("%o.%o",qq,AssociatedCharacter(qq,StringToInteger(t[1]),StringToInteger(t[2])));
end intrinsic;

intrinsic AssociatedPrimitiveCharacter (q::RngIntElt,n::RngIntElt) -> RngIntElt, RngIntElt
{ The primitive Conrey character qq.nn inducing the Conrey character q.n (returns qq and nn). }
    qq := Conductor(q,n);
    return qq, AssociatedCharacter(qq,q,n);
end intrinsic;

intrinsic AssociatedPrimitiveCharacter (s::MonStgElt) -> MonStgElt
{ Conrey character qq.nn of modulus qq induced by the primitive character inducing the Conrey character q.n. }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    q, n := AssociatedPrimitiveCharacter(StringToInteger(t[1]),StringToInteger(t[2]));
    return Sprintf("%o.%o",q,n);
end intrinsic;

intrinsic ConreyCharacterProduct (q1::RngIntElt, n1::RngIntElt, q2::RngIntElt, n2::RngIntElt) -> RngIntElt, RngIntElt
{ Computes the product q.n of the Conrey characters q1.n1 and q2.n2, returning q=LCM(q1,q2) and n. }
    if q1 eq 1 then return q2,n2; end if;
    if q2 eq 1 then return q1,n1; end if;
    q := LCM(q1,q2); return q,(AssociatedCharacter(q,q1,n1)*AssociatedCharacter(q,q2,n2)) mod q;
end intrinsic;

intrinsic ConreyCharacterProduct (s1::MonStgElt, s2::MonStgElt) -> MonStgElt
{ Computes the product q.n of the Conrey characters q1.n1 and q2.n2, returning the Conrey label q.n }
    t1 := Split(s1,"."); t2 := Split(s2,".");
    require #t1 eq 2 and #t2 eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return Sprintf("%o.%o",q,n) where q,n := ConreyCharacterProduct(atoi(t1[1]),atoi(t1[2]),atoi(t2[1]),atoi(t2[2]));
end intrinsic;

intrinsic ConreyInverse (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The Conrey index  of the inverse of the Conrey character q.n. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if q eq 1 then return 1; end if;
    return Integers()!((Integers(q)!n)^-1);
end intrinsic;

intrinsic ConreyInverse (s::MonStgElt) -> MonStgElt
{ The Conrey index  of the inverse of the Conrey character q.n. }
    t := Split(s,".");
    require #t eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return Sprintf("%o.%o",t[1],ConreyInverse(StringToInteger(t[1]),StringToInteger(t[2])));
end intrinsic;

intrinsic ConductorProductBound (M::RngIntElt, N::RngIntElt) -> RngIntElt
{ Quickly computes an integer guaranteed to divide the conductor of any product of Dirichlet characters of conductors M and N. }
    d := GCD(M,N);  m := LCM(M,N);
    return (m div d) * &*[Integers()|p^Valuation(d,p):p in PrimeDivisors(d)|Valuation(m,p) ne Valuation(d,p)];
end intrinsic;

intrinsic ConductorProduct (q1::RngIntElt, n1::RngIntElt, q2::RngIntElt, n2::RngIntElt) -> RngIntElt
{ The conductor of the product of the Conrey characters q1.n1 and q2.n2. }   
    c1 := Conductor(q1,n1);  c2 := Conductor(q2,n2);
    P := Set(PrimeDivisors(c1) cat PrimeDivisors(c2));
    c := 1; 
    for p in P do
        e1 := Valuation(c1,p);  e2 := Valuation(c2,p);
        if e1 ne e2 then c *:= p^Max(e1,e2); continue; end if;
        qp1 := p^Valuation(q1,p);  qp2 := p^Valuation(q2,p); cp := p^e1;
        n := (AssociatedCharacter(cp,qp1,n1 mod qp1)*AssociatedCharacter(cp,qp2,n2 mod qp2)) mod cp;
        if n eq 1 then continue; end if;
        c *:= p^(Valuation(Order(Integers(cp)!n),p)+1);
        if p eq 2 and e1 gt 2 and ConreyCharacterValue(cp,n,5) ne 1 then c *:= 2; end if;
    end for;
    return c;
end intrinsic;

intrinsic ConductorProduct (s1::MonStgElt, s2::MonStgElt) -> RngIntElt
{ The conductor of the product of the Conrey characters q1.n1 and q2.n2. }   
    t1 := Split(s1,"."); t2 := Split(s2,".");
    require #t1 eq 2 and #t2 eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return ConductorProduct(atoi(t1[1]),atoi(t1[2]),atoi(t2[1]),atoi(t2[2]));
end intrinsic;

intrinsic PrimitiveConductorProduct (q1::RngIntElt, n1::RngIntElt, q2::RngIntElt, n2::RngIntElt) -> RngIntElt
{ The conductor of the product of the primitive Conrey characters q1.n1 and q2.n2 (primitivity is not verified). }   
    P := Set(PrimeDivisors(q1) cat PrimeDivisors(q2));
    c := 1; 
    for p in P do
        e1 := Valuation(q1,p);  e2 := Valuation(q2,p);
        if e1 ne e2 then c *:= p^Max(e1,e2); continue; end if;
        R := Integers(p^e1); n := (R!n1)*(R!n2);
        if n eq 1 then continue; end if;
        c *:= p^(Valuation(Order(n),p)+1);
        if p eq 2 and e1 gt 2 and ConreyCharacterValue(2^e1,Integers()!n,5) ne 1 then c *:= 2; end if;
    end for;
    return c;
end intrinsic;

intrinsic PrimitiveConductorProduct (s1::MonStgElt, s2::MonStgElt) -> RngIntElt
{ The conductor of the product of the primitive Conrey characters q1.n1 and q2.n2 (primitivity not verified). }   
    t1 := Split(s1,"."); t2 := Split(s2,".");
    require #t1 eq 2 and #t2 eq 2: "Conrey labels have the form q.n where q and n are positive coprime integers";
    return PrimitiveConductorProduct(atoi(t1[1]),atoi(t1[2]),atoi(t2[1]),atoi(t2[2]));
end intrinsic;

intrinsic Twist (q1::RngIntElt, n1::RngIntElt, q2::RngIntElt, n2::RngIntElt) -> RngIntElt, RngIntElt
{ Given Conrey characters chi:=q1.n1 and psi:=q2.n2 returns the character tchi:=q.n of modulus q:=LCM(Mudulus(chi),Conductor(psi)*Conductor(chi*psi)) associated to chi*psi^2; if chi is minimal the twist of a twist-minimal newform f of character chi by psi will lie in S_k(q,tchi)^new. }
    q3,n3 := ConreyCharacterProduct (q1,n1,q2,n2);  q4,n4 := ConreyCharacterProduct (q3,n3,q2,n2);
    q := LCM(q1,Conductor(q2,n2)*Conductor(q3,n3));
    return q, AssociatedCharacter (q,q4,n4);
end intrinsic;

intrinsic Twist (s1::MonStgElt, s2::MonStgElt) -> MonStgElt
{ Given Conrey characters chi:=q1.n1 and psi:=q2.n2 returns the character tchi:=q.n of modulus q:=LCM(Mudulus(chi),Conductor(psi)*Conductor(chi*psi)) associated to chi*psi^2; if chi is minimal the twist of a twist-minimal newform f of character chi by psi will lie in S_k(q,tchi)^new. }
    s3 := ConreyCharacterProduct (s1,s2);  return AssociatedCharacter (LCM(Modulus(s1),Conductor(s2)*Conductor(s3)),ConreyCharacterProduct (s3,s2));
end intrinsic;

intrinsic Twist (chi::GrpDrchElt, psi::GrpDrchElt) -> GrpDrchElt
{ Given Dirichlet characters chi and psi returns the character tchi of modulus N:=LCM(Mudulus(chi),Conductor(psi)*Conductor(chi*psi)) associated to chi*psi^2; if chi is minimal the twist of a twist-minimal newform f of character chi by psi will lie in S_k(N,tchi)^new. }
    return DirichletCharacter(Twist(ConreyLabel(chi),ConreyLabel(psi)));
end intrinsic;

// Given an nth-root of unity z in a number field K return angles of conjugates (in standard order of embeddings of K)
function EmbeddedConjugateAngles(z,n)
    C := Conjugates(z);
    CC := Parent(z[1]);
    pi := Pi(RealField());
    return [ NormalizedAngle(Round(n*Argument(c)/(2*pi))/n) : c in C];
end function;

intrinsic ConreyConjugates (chi::GrpDrchElt, xi::Map: ConreyIndexList:=ConreyIndexes(chi)) -> SeqEnum[RngIntElt]
{ Given a Dirichlet character chi embedded as xi with values in a number field K, returns a list of the Conrey labels corresponding to the embeddings of K in C, as ordered by Conjugates. }
    if #ConreyIndexList eq 1 then return [ConreyIndexList[1]:i in [1..Degree(Codomain(xi))]]; end if;
    q := Modulus(chi);  e := Order(chi);
    S := UnitGenerators(chi);
    T := AssociativeArray();
    for n in ConreyIndexList do T[ConreyCharacterAngles(q,n,S)] := n; end for;
    A := [EmbeddedConjugateAngles(xi(m),e) : m in S];
    return [T[[A[i][j] : i in [1..#S]]] : j in [1..#A[1]]];
end intrinsic;

intrinsic TranslatedCharacterAngles (N::RngIntElt, u::SeqEnum[RngIntElt], v::SeqEnum, U::SeqEnum[RngIntElt]) -> SeqEnum[FldRatElt]
{ Given arbitrary generators u for (Z/NZ)* and a corresponding list of angles v defining a character of modulus N, compute a list of angles giving values of character on the integers in S.  Does not verify the validity of v! }
    require N ge 1: "Modulus N must be a positive integer";
    require #u eq #v: "You must specify an angle for each generator";
    require #u gt 0 and &and[(n mod N) ne 1 and GCD(N,n) eq 1:n in u]: "Generators must be coprime to N and not 1 modulo N.";
    v := [NormalizedAngle(x):x in v];
    if U eq u then return v; end if;  // Don't waste time on the (easy) expected case
    if N le 2 then return [Rationals()|1:n in U]; end if;
    evec := UnitGeneratorsLogMap(N,u);
    V := [NormalizedAngle(&+[e[i]*v[i]:i in [1..#u]]) where e:=evec(x): x in U];
    return V;
end intrinsic;

function TestCharacterAngles(M)
    for N:=3 to M do
        U := UnitGenerators(N);
        gm,pi := UnitGroup(Integers(N));
        for chi in CharacterOrbitReps(N) do
            L := ConreyIndexes(chi);
            for n in L do
                V := ConreyCharacterAngles(N,n,U);
                for i:=1 to 3 do
                    S := [Random(gm):i in [1..#U]];
                    while sub<gm|S> ne gm do S := [Random(gm):i in [1..#U]]; end while;
                    u := [Integers()!pi(s):s in S];
                    v := ConreyCharacterAngles(N,n,u);
                    assert TranslatedCharacterAngles(N,u,v,U) eq V;
                end for;
            end for;
        end for;
        printf "Passed three random tests for each Conrey character of modulus %o\n", N;
    end for;
    return true;
end function;

intrinsic DirichletCharacterFromAngles (N::RngIntElt,u::SeqEnum[RngIntElt],v::SeqEnum[FldRatElt]) -> GrpDrchElt
{ Given a modulus N, a list of generators for (Z/NZ)*, and a list of angles v returns the Dirichlet character with values in Q(zeta_n) mapping u[i] to zeta_n^(n*v[i]), where n is the LCM of the denominators in v. }
    require N gt 0: "Modulus N must a positive integer";
    if N lt 3 then assert #v eq 0; return DirichletGroup(N)!1; end if;
    V := TranslatedCharacterAngles(N,u,v,UnitGenerators(N)); // compute angles on standard Magma generators for (Z/NZ)*
    n := LCM([Denominator(e):e in V]);
    if n eq 1 then return DirichletGroup(N)!1; end if;
    if n eq 2 then return DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N),[(-1)^(Integers()!(n*e)) : e in V]); end if;
    F := CyclotomicField(n);
    return DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^(Integers()!(n*e)) : e in V]);
end intrinsic;

intrinsic DirichletCharacterFromAngles (N::RngIntElt,v::SeqEnum) -> GrpDrchElt
{ Given a modulus N, a positive integer n, a list of integers u giving standard generates for (Z/NZ)*, and a suitable list of integers v, returns the Dirichlet character with values in Q(zeta_n) mapping u[i] to zeta_n^v[i]. }
    require N gt 0: "Modulus N must a positive integer";
    if N lt 3 then assert #v eq 0; return DirichletGroup(N)!1; end if;
    n := LCM([Denominator(e):e in v]);
    if n eq 1 then return DirichletGroup(N)!1; end if;
    if n eq 2 then return DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N),[(-1)^(Integers()!(n*e)) : e in v]); end if;
    F := CyclotomicField(n);
    return DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^(Integers()!(n*e)) : e in v]);
end intrinsic;

intrinsic SquareRoots (chi::GrpDrchElt) -> SeqEnum[GrpDrchElt]
{ A list of the Dirichlet characters psi in the ambient group of chi for which psi^2 = chi (note that only psi in the ambient group of chi will be returned). }
    if IsOdd(Order(chi)) then
        psi := Sqrt(chi);   // this is just computing psi^e where e = 1/2 mod Order(chi), but we'll let Magma do it
    else
        // Deal with the even order case that Magma does not know how to handle
        u := UnitGeneratorOrders(chi);
        v := [r:r in CharacterAngles(chi)];
        if not &and[IsOdd(u[i]) or IsDivisibleBy(u[i],2*Denominator(v[i])):i in [1..#u]] then return [Parent(chi)|]; end if;
        psi := DirichletCharacterFromAngles (Modulus(chi), [r/2:r in v]);
    end if;
    assert psi^2 eq chi;
    // Every square root of chi is psi*xi for some 2-torsion element xi of G; such xi are precisely the rational characters returned by DirichletGroup
    return [Parent(chi)|psi*xi : xi in Elements(DirichletGroup(Modulus(chi)))];
end intrinsic;

intrinsic CyclotomicConreyCharacter (q::RngIntElt,n::RngIntElt) -> GrpDrchElt
{ The Dirichlet character with Conrey label q.n. }
    return DirichletCharacterFromAngles(q,UnitGenerators(q),ConreyCharacterAngles(q,n));
end intrinsic;

intrinsic CyclotomicConreyCharacter (s::MonStgElt) -> GrpDrchElt
{ The Dirichlet character with Conrey label q.n. }
    a := [StringToInteger(n):n in Split(s,".")];
    require #a eq 2 and a[2] gt 0 and a[1] gt a[2] and GCD(a[1],a[2]) eq 1: "Label should be either a Conrey label like 7.6.";
    return CyclotomicConreyCharacter (a[1],a[2]);
end intrinsic;

intrinsic DirichletCharacter (chi:GrpDrchElt) -> GrpDrchElt
{ The Dirichlet character. }
    return chi;
end intrinsic;

intrinsic DirichletCharacter (q::RngIntElt,n::RngIntElt) -> GrpDrchElt
{ The Dirichlet character with Conrey label q.n, equivalent to CyclotomicConreyCharacter(q,n). }
    return DirichletCharacterFromAngles(q,UnitGenerators(q),ConreyCharacterAngles(q,n));
end intrinsic;

intrinsic DirichletCharacter (label::MonStgElt) -> GrpDrchElt
{ Returns the Dirichlet character with the specified label (which may be a Conrey label q.n or a character orbit label N.x). }
    s := Split(label,".");
    require #s eq 2: "Label should be either a Conrey label like 7.6 or a charcter orbit label like 7.b.";
    N := atoi(s[1]);
    if s[2][1] ge "0" and s[2][1] le "9" then return CyclotomicConreyCharacter(N,atoi(s[2])); end if;
    require s[2][1] ge "a" and s[2][1] le "z":"Label should be either a Conrey label like 7.6 or a charcter orbit label like 7.b.";
    return CharacterOrbitRep(N,Base26Decode(s[2])+1);
end intrinsic;

intrinsic Conjugates (chi::GrpDrchElt) -> SeqEnum[GrpDrchElt]
{ List of Galois conjugates of chi. }
    N :=Modulus(chi); if N le 2 then return [chi]; end if;
    u := UnitGenerators(N); v := CharacterAngles(chi,u);
    return [Parent(chi)|DirichletCharacterFromAngles(N,u,w) : w in ConjugateAngles(v)];
end intrinsic;

intrinsic ConreyIndexes (chi::GrpDrchElt) -> SeqEnum[RngIntElt]
{ Sorted list of Conrey indexes of the Galois conjugates of the specified Dirichlet charatacter. }
    return Sort([ConreyIndex(psi):psi in Conjugates(chi)]);
end intrinsic;

intrinsic ConreyIndexes (s::MonStgElt) -> SeqEnum[RngIntElt]
{ Sorted list of integers n giving the Conrey labels q.n of the conjugates in the specifeid Galois orbit of modulus N. }
    t := SplitCharacterOrbitLabel(s);
    return ConreyIndexes (CharacterOrbitRep(t[1],t[2]));
end intrinsic;

intrinsic ConreyConjugates (q::RngIntElt,n::RngIntElt) -> SeqEnum[RngIntElt]
{ Returns a sorted list of Conrey indexes m of all Conrey characters q.m conjugate to q.n. }
    require GCD(q,n) eq 1: "n must be coprime to the modulus q";
    Zq := Integers(q);
    U,pi := UnitGroup(Zq);  m := Order(Zq!n);
    X := [pi(u):u in U|Order(u) eq m];
    if #X eq EulerPhi(m) then return Sort([Integers()|x:x in X]); end if;
    v := ConreyCharacterAngles(q,n);
    V := Set(ConjugateAngles(v));
    return Sort([Integers()|x:x in X|ConreyCharacterAngles(q,Integers()!x) in V]);
end intrinsic;

intrinsic ConreyConjugates (s::MonStgElt) -> SeqEnum[MonStgElt]
{ Returns a sorted list of labels of all Conrey characters q.m conjugate to specified Conrey character or in specified character orbit. }
    t := Split(s,".");
    require #t eq 2: "Label should be either a Conrey label like 7.6 or a character orbit label like 7.b.";
    q := StringToInteger(t[1]);
    if t[2][1] ge "a" and t[2][1] le "z" then
        n := ConreyIndex(DirichletCharacter(s));
    else
        require t[2][1] ge "0" and t[2][1] le "9":"Label should be either a Conrey label like 7.6 or a charcter orbit label like 7.b.";
        n := StringToInteger(t[2]);
    end if;
    return [t[1] cat "." cat IntegerToString(m): m in ConreyConjugates(q,n)];
end intrinsic;

intrinsic ConreyLabels (s::MonStgElt) -> SeqEnum[MonSTgElt]
{ Returns a sorted list of labels of all Conrey characters q.m conjugate to specified Conrey character or in specified character orbit. }
    return ConreyConjugates(s);
end intrinsic;

intrinsic ConreyOrbitTable (filename::MonStgElt, M::RngIntElt) -> SeqEnum[SeqEnum[RngIntElt]]
{ Given the name of input file containing records N:o:L:... where L is a list of Conrey indexes n of Conrey characters N.n with orbit index o, creates table T[N][n] := o. }
    require M gt 0: "Second argument must be a positive integer.";
    S := [Split(r,":"):r in Split(Read(filename))];
    T := [[0:n in [1..N]]:N in [1..M]];
    for r in S do N := StringToInteger(r[1]); if N le M then o := StringToInteger(r[2]); for n in StringToIntegerArray(r[3]) do T[N][n] := o; end for; end if; end for;
    return T;
end intrinsic;

intrinsic ConreyOrbitLabelTable (filename::MonStgElt,M::RngIntElt) -> SeqEnum[SeqEnum[MonStgElt]]
{ Given the name of input file containing records N:o:L:... where L is a list of Conrey indexes n of Conrey characters N.n with orbit index o, creates table T[N][n] := N.a where N.a is the lable of the character orbit of modulus N and index o. }
    require M gt 0: "Second argument must be a positive integer.";
    S := [Split(r,":"):r in Split(Read(filename))];
    T := [["":n in [1..N]]:N in [1..M]];
    for r in S do N:=atoi(r[1]); if N le M then s := r[1] cat "." cat Base26Encode(atoi(r[2])-1); for n in atoii(r[3]) do T[N][n]:=s; end for; end if; end for;
    return T;
end intrinsic;

intrinsic CharacterFromValues (N::RngIntElt,u::SeqEnum[RngIntElt],v::SeqEnum:Orbit:=false) -> Map
{ Given a modulus N, a list of generators of (Z/NZ)*, and a corresponding list of roots of unity in a number/cyclotomic field K, returns a map ZZ -> K for the Dirichlet character. }
    require N gt 0: "Modulus must be a positive integer";
    require #u eq #v: "List of unit generators and values must be lists of the same length";
    K := Universe(v);
    if N le 2 then psi:=map< Integers()->K | x :-> GCD(N,x) eq 1 select 1 else 0 >; if Orbit then return psi,1; else return psi; end if; end if;
    A,pi := UnitGroup(Integers(N)); ipi:=Inverse(pi);
    u0 := [pi(A.i):i in [1..NumberOfGenerators(A)]];
    if u ne u0 then
        f := UnitGeneratorsLogMap(N,u);
        v0 := [prod([v[i]^e[i]:i in [1..#u]]) where e:=f(g):g in u0];
        u := u0; v := v0;
    end if;
    psi := map< Integers()->K | x :-> GCD(N,x) eq 1 select &*[v[i]^(Eltseq(ipi(x))[i]):i in [1..#v]] else K!0>;
    if not Orbit then return psi; end if;
    // if Orbit flag is set, determine the character orbit by comparing traces (note that we need tot take traces from the subfield of K generated by the image of psi)
    m := LCM([Min([d:d in Divisors(EulerPhi(N))|z^d eq 1]):z in v]);
    d := EulerPhi(m); e := ExactQuotient(Degree(K),d);
    t := [ExactQuotient(Trace(psi(n)),e) : n in [1..N]];
    G := CharacterOrbitReps(N);
    M := [i : i in [1..#G] | Order(G[i]) eq m and [Trace(z):z in ValueList(G[i])] eq t];
    assert #M eq 1;
    return psi,M[1];
end intrinsic;

intrinsic Order (xi::Map, N::RngIntElt) -> RngIntElt
{ Given a map xi:ZZ -> K that is a Dirichlet character of modulus N, returns its order (results are undefined if xi is not of modulus N). }
    e := Exponent(MultiplicativeGroup(Integers(N)));
    U := UnitGenerators(DirichletGroup(N));
    return LCM([Min([d: d in Divisors(e)|a^d eq 1]) where a:=xi(u) : u in U]);
end intrinsic;

intrinsic Conductor (xi::Map, N::RngIntElt) -> RngIntElt
{ Given a map ZZ -> K that is a Dirichlet character of modulus N, returns its conductor (results are undefined if xi is not of modulus N). }
    U := UnitGenerators(DirichletGroup(N));
    V := [xi(u):u in U];
    if Set(V) eq {1} then return 1; end if;
    if IsPrime(N) then return N; end if;
    return Min([M : M in Divisors(N) | M gt 2 and &and[&and[xi(u) eq xi(u+r*M):r in [1..ExactQuotient(N,M)-1]]:u in U]]);
end intrinsic;

intrinsic Degree (xi::Map, N::RngIntElt) -> RngIntElt
{ Given a map ZZ -> K that is a Dirichlet character of modulus N, returns the degree of the (cyclotomic) subfield of K generated by its image. }
    U := UnitGenerators(DirichletGroup(N));
    if #U eq 0 then return 1; end if;
    if Codomain(xi) eq Rationals() then return {xi(u):u in U} eq {1} select 1 else 2; end if;
    return Degree(sub<Codomain(xi) | [xi(u) : u in U]>);
end intrinsic;

intrinsic Parity (xi::Map) -> RngIntElt
{ Given a map ZZ -> K that is a Dirichlet character, returns its parity xi(-1). }
    return Integers()!xi(-1);
end intrinsic;

intrinsic IsReal (xi::Map, N::RngIntElt) -> Bool
{ Given a map ZZ -> K that is a Dirichlet character, returns a boolean indicating whether the character takes only real values (trivial or quadratic) or not. }
    return Order(xi,N) le 2;
end intrinsic;


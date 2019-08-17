intrinsic sum(X::[]) -> .
{ Sum of a sequence (empty sum is 0). }
    return #X eq 0 select Universe(X)!0 else &+X;
end intrinsic;

intrinsic sum(v::ModTupRngElt) -> .
{ Sum of a vector. }
    return  sum(Eltseq(v));
end intrinsic;

intrinsic prod(X::[]) -> .
{ Product of a sequence (empty product is 1). }
    return #X eq 0 select Universe(X)!1 else &*X;
end intrinsic;

intrinsic prod(v::ModTupRngElt) -> .
{ Product of a vector. }
    return prod(Eltseq(v));
end intrinsic;

intrinsic strip(X::MonStgElt) -> MonStgElt
{ Strips spaces and carraige returns from string; much faster than StripWhiteSpace. }
    return Join(Split(Join(Split(X," "),""),"\n"),"");
end intrinsic;

intrinsic sprint(X::.) -> MonStgElt
{ Sprints object X with spaces and carraige returns stripped. }
    return strip(Sprintf("%o",X));
end intrinsic;

intrinsic atoi(s::MonStgElt) -> RngIntElt
{ Converts a string to an integer (alias for StringToInteger). }
    return StringToInteger(s);
end intrinsic;

intrinsic StringToIntegerArray(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Given string representing a sequence of integers, returns the sequence (faster and safer than eval). }
    t := strip(s);
    if t eq "[]" then return []; end if;
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [StringToInteger(n):n in Split(t[2..#t-1],",")];
end intrinsic;

intrinsic atoii(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of integers (alias for StringToIntegerArray). }
    return StringToIntegerArray(s);
end intrinsic;

intrinsic atoiii(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of sequences of integers (alias for StringToIntegerArray). }
    t := strip(s);
    if t eq "[]" then return []; end if;
    if t eq "[[]]" then return [[Integers()|]]; end if;
    assert #t gt 4 and t[1..2] eq "[[" and t[#t-1..#t] eq "]]";
    r := Split(t[2..#t-2],"[");
    return [[Integers()|StringToInteger(n):n in Split(Split(a,"]")[1],",")]:a in r];
end intrinsic;

intrinsic StringToRationalArray(s::MonStgElt) -> SeqEnum[RatFldElt]
{ Given string representing a sequence of rational numbers, returns the sequence (faster and safer than eval). }
    if s eq "[]" then return []; end if;
    t := strip(s);
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [StringToRational(n):n in Split(t[2..#t-1],",")];
end intrinsic;

intrinsic nfdisc(f::RngUPolElt) -> RngIntElt
{ Given a polynomial with rational coefficients, returns the integer absolute discriminant of the number field it defines. }
    return Integers()!Discriminant(RingOfIntegers(NumberField(PolynomialRing(Rationals())!f)));
end intrinsic;

intrinsic nfdisc(f::SeqEnum) -> RngIntElt
{ Given a polynomial with rational coefficients, returns the integer absolute discriminant of the number field it defines. }
    return Integers()!Discriminant(RingOfIntegers(NumberField(PolynomialRing(Rationals())!f)));
end intrinsic;

intrinsic facpat(f::RngUPolElt) -> SetMulti[RngIntElt]
{ Returns the factorization pattern of the univariate polynomial f(x) (specificed by its coefficients). }
    return {*Degree(a[1])^^a[2]:a in Factorization(f)*};
end intrinsic;

intrinsic facpat(f::SeqEnum[RngIntElt]) -> SetMulti[RngIntElt]
{ Returns the factorization pattern of the univariate polynomial f(x) (specificed by its coefficients). }
    return facpat(PolynomialRing(Integers())!f);
end intrinsic;

intrinsic frobord(f::RngUPolElt,p::RngIntElt) -> RngIntElt
{ Returns the LCM of the degrees of the factors of the polynomial f reduced modulo the prime p. }
    return LCM(facpat(ChangeRing(f,GF(p))));
end intrinsic;

intrinsic frobord(f::SeqEnum[RngIntElt],p::RngIntElt) -> RngIntElt
{ Returns the LCM of the degrees of the factors of the polynomial with coefficients specified by f reduced modulo the prime p. }
    return LCM(facpat(PolynomialRing(GF(p))!f));
end intrinsic;

intrinsic goodp(f::RngUPolElt,p::RngIntElt) -> RngIntElt
{ Returns true if the speicified polynomial is square free modulo p. }
    return Discriminant(PolynomialRing(GF(p))!f) ne 0;
end intrinsic;

intrinsic goodp(f::SeqEnum[RngIntElt],p::RngIntElt) -> RngIntElt
{ Returns the LCM of the degrees of the factors of the polynomial with coefficients specified by f reduced modulo the prime p. }
    return Discriminant(PolynomialRing(GF(p))!f) ne 0;
end intrinsic;

intrinsic Base26Encode(n::RngIntElt) -> MonStgElt
{ Given a nonnegative integer n, returns its encoding in base-26 (a=0,..., z=25, ba=26,...). }
    require n ge 0: "n must be a nonnegative integer";
    alphabet := "abcdefghijklmnopqrstuvwxyz";
    s := alphabet[1 + n mod 26]; n := (n-(n mod 26)) div 26;
    while n gt 0 do
        s := alphabet[1 + n mod 26] cat s; n := (n-(n mod 26)) div 26;
    end while;
    return s;
end intrinsic;

intrinsic Base26Decode(s::MonStgElt) -> RngIntElt
{ Given string representing a nonnegative integer in base-26 (a=0,..., z=25, ba=26,...) returns the integer. }
    alphabetbase := StringToCode("a");
    n := 0;
    for c in Eltseq(s) do n := 26*n + StringToCode(c) - alphabetbase; end for;
    return n;
end intrinsic;

// This implementation is slow and suitable only for small groups
intrinsic PolycyclicPresentation(gens::SeqEnum,m::UserProgram,id::.) -> SeqEnum[RngIntElt], Map
{ Given a sequence of generators in a uniquely represented hashable polycyclic group with composition law m and identity element id, returns sequence of relative orders and a map from group elements to exponent vectors.}
    r := [Integers()|];
    if #gens eq 0 then return r, func<a|r>; end if;
    n := #gens;
    T := [Universe(gens)|id];
    while true do g := m(T[#T],gens[1]); if g eq id then break; end if; Append(~T,g); end while;
    Append(~r,#T);
    for i:=2 to n do
        X := Set(T); S := T; j := 1;
        g := gens[i];  h := g; while not h in X do S cat:= [m(t,h):t in T]; h := m(h,g); j +:= 1; end while;
        Append(~r,j);  T := S;
    end for;
    ZZ := Integers();
    A := AssociativeArray(Universe(gens));
    for i:=1 to #T do A[T[i]] := i-1; end for;
    rr := [ZZ|1] cat [&*r[1..i-1]:i in [2..n]];
    return r, func<x|[Integers()|(e div rr[i]) mod r[i] : i in [1..n]] where e:=A[x]>;
end intrinsic;

intrinsic OrderStats(G::Grp) -> SetMulti[RngIntElt]
{ Multiset of order statistics of elements of the group G. }
    C:=Classes(G);
    return SequenceToMultiset(&cat[[c[1]:i in [1..c[2]]]:c in C]);
end intrinsic;

intrinsic IndexFibers (S::[], f::UserProgram) -> Assoc
{ Given a list of objects S and a function f on S creates an associative array satisfying A[f(s)] = [t:t in S|f(t) eq f(s)]. }
    A := AssociativeArray();
    for x in S do
        y := f(x);
        A[y] := IsDefined(A,y) select Append(A[y],x) else [x];
    end for;
    return A;
end intrinsic;

intrinsic ReduceToReps (S::[], E::UserProgram) -> SeqEnum
{ Given a list of objects S and an equivalence relation E on S returns a maximal sublist of inequivalent objects. }
    if #S le 1 then return S; end if;
    if #S eq 2 then return E(S[1],S[2]) select [S[1]] else S; end if;
    T:=[S[1]];
    for i:=2 to #S do
        s:=S[i]; sts:=true;
        for j:=#T to 1 by -1 do // check most recently added entries first in case adjacent objects in S are more likely to be equivalent (often true)
            if E(s,T[j]) then sts:=false; break; end if;
        end for;
        if sts then T:=Append(T,s); end if;
    end for;
    return T;
end intrinsic;

intrinsic Classify (S::[], E::UserProgram) -> SeqEnum[SeqEnum]
{ Given a list of objects S and an equivalence relation E on them returns a list of equivalence classes (each of which is a list). }
    if #S eq 0 then return []; end if;
    if #S eq 1 then return [S]; end if;
    if #S eq 2 then return E(S[1],S[2]) select [S] else [[S[1]],[S[2]]]; end if;
    T:=[[S[1]]];
    for i:=2 to #S do
        s:=S[i]; sts:=true;
        for j:=#T to 1 by -1 do // check most recently added classes first in case adjacent objects in S are more likely to be equivalent (often true)
            if E(s,T[j][1]) then T[j] cat:= [s]; sts:=false; break; end if;
        end for;
        if sts then T:=Append(T,[s]); end if;
    end for;
    return T;
end intrinsic;

intrinsic DihedralGroup(G::GrpAb) -> Grp
{ Construct the generalized dihedral group dih(G) := G semidirect Z/2Z with Z/2Z acting by inversion. }
    Z2 := AbelianGroup([2]);
    h:=hom<Z2->AutomorphismGroup(G)|x:->hom<G->G|g:->IsIdentity(x) select g else -g>>;
    return SemidirectProduct(G,Z2,h);
end intrinsic;

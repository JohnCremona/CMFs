intrinsic sum(X::[]) -> .
{ Sum of a sequence (empty sum is 0). }
    return #X eq 0 select 0 else &+X;
end intrinsic;

intrinsic prod(X::[]) -> .
{ Product of a sequence (empty product is 1). }
    return #X eq 0 select 1 else &*X;
end intrinsic;

intrinsic strip(X::MonStgElt) -> MonStgElt
{ Strips spaces and carraige returns from string; much faster than StripWhiteSpace. }
    return Join(Split(Join(Split(X," "),""),"\n"),"");
end intrinsic;

intrinsic sprint(X::.) -> MonStgElt
{ Sprints object X with spaces and carraige returns stripped. }
    return strip(Sprintf("%o",X));
end intrinsic;

intrinsic StringToIntegerArray(s::MonStgElt) -> SeqEnum[RntIntElt]
{ Given string representing a sequence of integers, returns the sequence (faster and safer than eval). }
    if s eq "[]" then return []; end if;
    t := strip(s);
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [StringToInteger(n):n in Split(t[2..#t-1],",")];
end intrinsic;

intrinsic StringToRationalArray(s::MonStgElt) -> SeqEnum[RatFldElt]
{ Given string representing a sequence of rational numbers, returns the sequence (faster and safer than eval). }
    if s eq "[]" then return []; end if;
    t := strip(s);
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [StringToRational(n):n in Split(t[2..#t-1],",")];
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

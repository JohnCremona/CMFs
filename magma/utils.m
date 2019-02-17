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

intrinsic Base26Encode(n::RntIntElt) -> MonStgElt
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

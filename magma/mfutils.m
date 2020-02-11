// Attach("utils.m");

intrinsic NewformLabel(N::RngIntElt,k::RngIntElt,o::RngIntElt,n::RngIntElt) -> MonStgElt
{ Given positive integers N,k,o,n specifying the level, weight, char orbit, Hecke orbit of newform, return the label of the newform. }
    require N gt 0 and k gt 0 and o gt 0 and n gt 0: "Inputs to NewformLabel must be positive integers.";
    return Join([IntegerToString(N),IntegerToString(k),Base26Encode(o-1),Base26Encode(n-1)],".");
end intrinsic;

intrinsic SplitNewformLabel(s::MonStgElt) -> RngIntElt,RngIntElt,RngIntElt,RngIntElt
{ Given the label N.k.a.x of a newform, return the level N, weight k, char orbit (as an integer), Hecke orbit (as an integer). }
    r := Split(s,".");
    return [StringToInteger(r[1]),StringToInteger(r[2]),Base26Decode(r[3])+1,Base26Decode(r[4])+1];
end intrinsic;

intrinsic SplitEmbeddedNewformLabel(s::MonStgElt) -> RngIntElt,RngIntElt,RngIntElt,RngIntElt
{ Given the label N.k.a.x.n.i of a newform, return the level N, weight k, char orbit (as an integer), Hecke orbit (as an integer), Conrey index n, relative embedding index i. }
    r := Split(s,".");
    return [StringToInteger(r[1]),StringToInteger(r[2]),Base26Decode(r[3])+1,Base26Decode(r[4])+1,StringToInteger(r[5]),StringToInteger(r[6])];
end intrinsic;

intrinsic CompareNewformLabels(s::MonStgElt,t::MonStgElt) -> RngIntElt
{ Compares newform label strings of the form N.k.a.x lexicographically bu level N, weight k, char orbit a, Hecke orbit x, returns -1,0,1. }
    return s eq t select 0 else (SplitNewformLabel(s) lt SplitNewformLabel(t) select -1 else 1);
end intrinsic;

intrinsic CompareEmbeddedNewformLabels(s::MonStgElt,t::MonStgElt) -> RngIntElt
{ Compares newform label strings of the form N.k.a.x lexicographically bu level N, weight k, char orbit a, Hecke orbit x, returns -1,0,1. }
    return s eq t select 0 else (SplitEmbeddedNewformLabel(s) lt SplitEmbeddedNewformLabel(t) select -1 else 1);
end intrinsic;

intrinsic NewspaceLabel(N::RngIntElt,k::RngIntElt,o::RngIntElt) -> MonStgElt
{ Given positive integers N,k,a specifying the level, weight, char orbit of a newspace, return the label of the newspace. }
    require N gt 0 and k gt 0 and o gt 0: "Inputs to NewspaceLabel must be positive integers.";
    return Join([IntegerToString(N),IntegerToString(k),Base26Encode(o-1)],".");
end intrinsic;

intrinsic SplitNewspaceLabel(s::MonStgElt) -> RngIntElt, RngIntElt, RngIntElt
{ Given the label N.k.a of a newspace, return the level N, weight k, char orbit a. }
    r := Split(s,".");
    return StringToInteger(r[1]),StringToInteger(r[2]),Base26Decode(r[3])+1;
end intrinsic;

intrinsic CompareNewspaceLabels(s::MonStgElt,t::MonStgElt) -> RngIntElt
{ Compares newspace label strings of the form N.k.o lexicographically bu level N, weight k, char orbit o, returns -1,0,1. }
    return s eq t select 0 else (SplitNewspaceLabel(s) lt SplitNewspaceLabel(t) select -1 else 1);
end intrinsic;

intrinsic Gamma1Label(N::RngIntElt,k::RngIntElt) -> MonStgElt
{ Given positive integers N,k specifying the level, weight of a space of newforms for Gamma1(N), return the lable of the space. }
    require N gt 0 and k gt 0: "Inputs to Gamma1Label must be positive integers.";
    return Join([IntegerToString(N),IntegerToString(k)],".");
end intrinsic;

intrinsic SplitGamma1Label(s::MonStgElt) -> RngIntElt, RngIntElt
{ Given the label N.k of S_k^new(Gamma1(N)), return the level N, weight k. }
    r := Split(s,".");
    return StringToInteger(r[1]),StringToInteger(r[2]);
end intrinsic;

// encode Hecke orbit as a 64-bit integer
intrinsic HeckeOrbitCode (N::RngIntElt,k::RngIntElt,o::RngIntElt,n::RngIntElt) -> RngIntElt
{ Given positive integers N,k,o,n specifying the level, weight, char orbit, Hecke orbit of newform, return the 64-bit Hecke orbit code of the newform. }
    require N gt 0 and k gt 0 and o gt 0 and n gt 0: "Inputs to NewformLabel must be positive integers.";
    require N lt 2^24: "Level N must be less than 2^24.";
    require k lt 2^12: "Weight k must be less than 2^12.";
    require o lt 2^16: "Char orbit index o must be less than 2^16.";
    require n lt 2^12: "Hecke oribt index n must be less than 2^11.";
    return N+2^24*k+2^36*(o-1)+2^52*(n-1);
end intrinsic;

// extract Hecke orbit invariants from code
intrinsic SplitHeckeOrbitCode(c::RngIntElt) -> RngIntElt, RngIntElt, RngIntElt, RngIntElt
{ Given the 64-bit Hecke orbit code of a newform, return the level, weight, char orbit, Hecke orbit of the newform. }
    N := c mod 2^24;  c := ExactQuotient(c-N,2^24);
    k := c mod 2^12;  c := ExactQuotient(c-k,2^12);
    o := (c mod 2^16)+1; c := ExactQuotient(c-(o-1),2^16);
    n := c+1;
    return N,k,o,n;
end intrinsic;


// Convert ap's to an's using multiplicativity and recurrence a_{pq} = a_p*a_q - chi(p)*p^(k-1)*a_q/p for q a power of p
intrinsic anlist_from_aplist (N::RngIntElt, k::RngIntElt, chi::Map, ap::[], m::RngIntElt : FactorTable:=[[q[1]^q[2]:q in Factorization(n)]:n in [1..m]]) -> []
{ Given level N, weight k, character chi (as a map form Z to the universe of ap), sequence of ap's, returns corresponding sequences of an's for n up to sepcified bound m. }
    P := PrimesInInterval(1,m);
    assert #P le #ap;
    an :=[Universe(ap)|0:i in [1..m]];
    an[1] := 1;
    for i:=1 to #P do
        an[P[i]] := ap[i];
        p := P[i]; q := p;
        while p*q le m do
            an[p*q] := an[p]*an[q];
            if not IsDivisibleBy(N,p) then an[p*q] -:= chi(p)*p^(k-1)*an[q div p]; end if;
            q *:= p;
        end while;
    end for;
    for n := 6 to m do an[n] := prod([an[q]:q in FactorTable[n]]); end for;
    return an;
end intrinsic;

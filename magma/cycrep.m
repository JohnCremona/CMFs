// empty sum is 0, empty product is 1
function sum(X) return #X eq 0 select 0 else &+X; end function;
function prod(X) return #X eq 0 select 1 else &*X; end function;

intrinsic DiscreteLogMap (z::RngElt,n::RngIntElt) -> Map
{ Given an nth root of unity z, returns the mapping z^e -> e for e in [0..n-1], and 0 otherwise. }
    R := Parent(z);
    T := AssociativeArray(R);
    zz := R!1;
    for i:=0 to n-1 do T[zz] := i; zz *:= z; end for;
    return map<R->Integers() | x :-> IsDefined(T,x) select T[x] else -1>;
end intrinsic;

intrinsic SparseZetaReduce(v::SeqEnum,n::RngIntElt) -> SeqEnum
{ For v in sparse zeta reprsentation and n odd, eliminates all terms in v of the form c*z^e with e > n/2. }
    if IsOdd(n) then return v; end if;
    m := n div 2;
    for i:=1 to #v do if v[i][2] ge m then v[i][1] := -v[i][1]; v[i][2] -:= m; end if; end for;
    return [x : x in Sort(v,func<a,b|a[2]-b[2]>) | x[1] ne 0];
end intrinsic;

intrinsic TwoSparseZetaRep(a::RngElt,z::RngElt,n::RngIntElt,dlog::Map) -> SeqEnum
{ Given an element a that is the sum of at most two powers of z, returns its sparse zeta representation. }
    if a eq 0 then return []; end if;
    e := dlog(a);
    if e ge 0 then return [<1,e>]; end if;
    zz := Parent(z)!1;
    v := [];
    for e1:=0 to n-1 do
        e2 := dlog(a-zz);
        if e2 ge 0 then v := e1 lt e2 select [<1,e1>,<1,e2>] else [<1,e2>,<1,e1>]; break; end if;
        zz *:= z;
    end for;
    if #v eq 0 then error "Unable to find 2-sparse cyclotomic representation"; end if;
    return v;
end intrinsic;

intrinsic SparseZetaAdd(a::SeqEnum,b::SeqEnum) -> SeqEnum
{ Add two elements in sparse zeta represtentation. }
    if #a eq 0 and #b eq 0 then return []; end if;
    c := Sort(a cat b, func<x,y|x[2]-y[2]>);
    d := [c[1]]; j:=1;
    for i:=2 to #c do
        if c[i][2] eq d[j][2] then d[j][1] +:= c[i][1]; else j+:=1; d[j] := c[i]; end if;
    end for;
    return d;
end intrinsic;

intrinsic SparseZetaSub(a::SeqEnum,b::SeqEnum) -> SeqEnum
{ Subtract two elements in sparse zeta represtentation. }
    if #a eq 0 and #b eq 0 then return []; end if;
    c := Sort(a cat [<-x[1],x[2]>: x in b], func<x,y|x[2]-y[2]>);
    d := [c[1]]; j:=1;
    for i:=2 to #c do
        if c[i][2] eq d[j][2] then d[j][1] +:= c[i][1]; else j+:=1; d[j] := c[i]; end if;
    end for;
    return d;
end intrinsic;

intrinsic SparseZetaMult(a::SeqEnum,b::SeqEnum,n::RngIntElt) -> SeqEnum
{ Multiply two elements in sparse zeta represtentation. }
    c := [];
    for x in a do
        r := [<x[1]*y[1],(x[2]+y[2]) mod n> : y in b];
        c := SparseZetaAdd (c, r);
    end for;
    return c;
end intrinsic;
    
intrinsic SparseZetaEval(a::SeqEnum,z::RngElt) -> RngElt
{ Evaluates sparse zeta representation yielding an element of the ring containing z. }
    return sum([x[1]*z^x[2]:x in a]);
end intrinsic;

intrinsic SparseZetaWeightOneCoefficients (ap::SeqEnum[FldNumElt],xi::Map,z::FldNumElt,n::RngIntElt) -> SeqEnum
{ Given the sequence of ap's of a weight one newform with coefficients in a number field K and its character xi: ZZ -> K, compute the sparse zeta rep of an's using given nth root of unity z in K.}
    m := NthPrime(#ap+1)-1;
    P := PrimesInInterval(1,m);
    an := [[]:i in [1..m]];
    an[1] := [<1,0>];
    dlog := DiscreteLogMap(z,n);
    for i:=1 to #P do
        an[P[i]] := SparseZetaReduce(TwoSparseZetaRep(ap[i],z,n,dlog),n);
        p := P[i]; q := p;
        chip := SparseZetaReduce(TwoSparseZetaRep(xi(p),z,n,dlog),n);
        while p*q le m do
            an[p*q] := SparseZetaReduce(SparseZetaMult(an[p],an[q],n),n);
            if #chip gt 0 then an[p*q] := SparseZetaReduce(SparseZetaSub(an[p*q],SparseZetaMult(chip,an[q div p],n)),n); end if;
            q *:= p;
        end while;
    end for;
    for i := 6 to m do
        Q := [q[1]^q[2]:q in Factorization(i)];
        if i ne Q[1] then an[i] := an[Q[1]]; end if;
        for j:=2 to #Q do an[i] := SparseZetaReduce(SparseZetaMult(an[i],an[Q[j]],n),n); end for;
    end for;
    return an;
end intrinsic;

intrinsic SparseZetaWeightOnePrimeCoefficients (ap::SeqEnum[FldNumElt],z::FldNumElt,n::RngIntElt) -> SeqEnum
{ Given the sequence of ap's of a weight one newform with coefficients in a number field K and its character xi: ZZ -> K, compute the sparse zeta rep of ap's using given nth root of unity z in K.}
    dlog := DiscreteLogMap(z,n);
    return [SparseZetaReduce(TwoSparseZetaRep(a,z,n,dlog),n):a in ap];
end intrinsic;

intrinsic SparseZetaCharacterValues (xi::Map,z::FldNumElt,n::RngIntElt,u::SeqEnum) -> SeqEnum
{ Given a character xi: ZZ -> K with values in Q(z) subset K, with z an nth root of unity, and a list of integers u returns sparse zeta rep of values of xi on u. }
    dlog := DiscreteLogMap(z,n);
    return [SparseZetaReduce(TwoSparseZetaRep(xi(x),z,n,dlog),n):x in u];
end intrinsic;

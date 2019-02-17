// Dependencies
// Attach("chars.m");
// Attach("polredabs.m")

intrinsic NFDiscriminant (f::RngUPolElt) -> RngIntElt
{ Given an irreducible polynomial in Q[x] returns the discriminant of the number field it defines. }
    return Integers()!Discriminant(RingOfIntegers(NumberField(f)));
end intrinsic;

intrinsic NFDiscriminant (f::SeqEnum) -> RngIntElt
{ Given an irreducible polynomial in Q[x] returns the discriminant of the number field it defines. }
    return Integers()!Discriminant(RingOfIntegers(NumberField(PolynomialRing(Rationals())!f)));
end intrinsic;

intrinsic NFFactoredDiscriminant (f::RngUPolElt) -> RngIntElt, SeqEnum
{ Given an irreducible polynomial in Q[x] returns the discriminant of the number field it defines along with its factorization. }
    D := NFDiscriminant(f);
    return D, Factorization(D);
end intrinsic;

intrinsic NFFactoredDiscriminant (f::SeqEnum) -> RngIntElt, SeqEnum
{ Given an irreducible polynomial in Q[x] returns the discriminant of the number field it defines along with its factorization. }
    D := NFDiscriminant(f);
    return D, Factorization(D);
end intrinsic;

intrinsic MinimalSubSibling (f::RngUPolElt:SplitDegree:=0) -> RngUPolElt
{ Given an irreducible polynomial f in Q[x] returns a polynomial g with the same splitting field as f with both the degree of g and |disc(Q[x]/(g))| minimal among those g for which Q[x]/(g(x)) lies in Q[x]/(f(x)); this will be the minimal sibling if Q[x]/(f(x)) is Galois. }
    if SplitDegree eq 0 then SplitDegree := #GaloisGroup(f); end if;
    K := NumberField(f);
    L := Sort([DefiningPolynomial(L[1]):L in Subfields(K)],func<a,b|Degree(a)-Degree(b)>);
    h := f; dh := Degree(h); Dh := 0;
    for g in L do
        if Degree(g) eq dh and #GaloisGroup(g) eq SplitDegree then Dg := Abs(NFDiscriminant(g)); if Dg lt Dh then h := g; Dh := Dg; end if; end if;
        if Degree(g) lt dh and #GaloisGroup(g) eq SplitDegree then h := g; dh := Degree(h); Dh := NFDiscriminant(h); end if;
    end for;
    return h;
end intrinsic;

intrinsic MinimalSubSibling (f::SeqEnum:SplitDegree:=0) -> SeqEnum
{ Given an irreducible polynomial f in Q[x] returns a polynomial g with the same splitting field as f with both the degree of g and |disc(Q[x]/(g))| minimal among those g for which Q[x]/(g(x)) lies in Q[x]/(f(x)); this will be the minimal sibling if Q[x]/(f(x)) is Galois. }
    return Eltseq(MinimalSubSibling(PolynomialRing(Rationals())!f:SplitDegree:=SplitDegree));
end intrinsic;

intrinsic MinimalCentralSibling (f::RngUPolElt) -> RngUPolElt
{ Given an irreducible polynomial f in Q[x] returns an irreducible polynomial g of minimal degree and minimal |disc(Q[x]/(g))|) such that the splitting field of g is the fixed field of the center of the Galois group of f. }
    L := SplittingField(f);
    G := AutomorphismGroup(L);
    K := FixedField(L,Center(G));
    if Degree(K) eq 1 then return [1,0]; end if;
    H := quo<G|Center(G)>;
    if IsAbelian(H) then return DefiningPolynomial(K); end if;
    return MinimalSubSibling(Polredbest(DefiningPolynomial(K)):SplitDegree:=#H);
end intrinsic;

intrinsic MinimalCentralSibling (f::SeqEnum) -> SeqEnum
{ Given an irreducible polynomial f in Q[x] returns an irreducible polynomial g of minimal degree and minimal |disc(Q[x]/(g))|) such that the splitting field of g is the fixed field of the center of the Galois group of f. }
    return Eltseq(MinimalCentralSibling(PolynomialRing(Rationals())!f));
end intrinsic;

intrinsic NFPolyIsIsomorphic (f::RngUPolElt,g::RngUPolElt) -> BoolElt
{ Determines whether the specified polynomials are monic irreducible elements of Q[x] that define the same number field. }
    if Degree(f) ne Degree(g) then return false; end if;
    if not (IsMonic(f) and IsMonic(g)) then return false; end if;
    if not (IsIrreducible(f) and IsIrreducible(g)) then return false; end if;
    if f eq g or Evaluate(f,-Parent(f).1) eq g then return true; end if;
    if Degree(f) le 24 then
        Rf<t>:=PolynomialRing(NumberField(f));
        return #Roots(Rf!Coefficients(g)) gt 0; // if g has a root in Q[x]/(f) then Q[x]/(g) is contained in Q[x]/(f) and we have equality because degrees match
    else
        Kf := NumberField(f);  Kg := NumberField(g);
        if Signature(Kf) ne Signature(Kg) then return false; end if;
        return IsIsomorphic(NumberField(f),NumberField(g));
    end if;
end intrinsic;

intrinsic NFPolyIsIsomorphic (f::SeqEnum,g::SeqEnum) -> BoolElt
{ Determines whether the specified sequences specify irreducible polynomials that define the same number field. }
    R<x> := PolynomialRing(Rationals());
    return NFPolyIsIsomorphic (R!f,R!g);
end intrinsic;

intrinsic OptimizedOrderBasis(KPoly::SeqEnum,ZSeq::SeqEnum[SeqEnum]:KBestPoly:=[],KBestIsPolredabs:=false,KDisc:=0,Verbose:=false,GeneratorBoundOnly:=false) -> 
    SeqEnum[RngInt], SeqEnum[SeqEnum[RngIntElt]], SeqEnum[SeqEnum[RngIntElt]],  RngIntElt, RngIntElt, BoolElt, RngIntElt
{ Given the coefficients of an irreducible monic polynomial f in Q[x] and a sequence of algebraic integers in the number field Q[x]/(f(x)) specified in terms of the power basis, returns:
    (1) list of integer coefficients of an optimized monic poly for K;
    (2) list of lists of rationals giving an optimized basis for the order O generated by Zvals;
    (3) list of list of lists integers specifying expressing input sequence in terms of optimized basis;
    (4) integer dividing the index of O in the ring of integers OK;
    (5) disc(OK) if known, zero otherwise;
    (6) boolean value set to true if the canonical polredabs polynomial defining K was used;
    (7) integer giving the least m such that the first m entries of the sequence generate the order O (as a ring). }
    
    require KPoly[#KPoly] eq 1: "First argument must specify the coefficients of a monic polynomial";
    deg := #KPoly-1;
    require &and[#z eq deg:z in ZSeq]: "Second argument must be a list of lists each of length 1 less then length of first argument";

    if deg eq 1 then return [1,0],[[1]], ZSeq, GCD([z[1]:z in ZSeq]), 1, 1; end if;

    if Verbose then start := Cputime(); end if;
    R<x>:=PolynomialRing(Rationals());
    K := NumberField(R!KPoly);
    Z := Matrix(Rationals(),ZSeq);
    KDisc := Integers()!KDisc;

    // Make best field if KBestPoly is not specified
    if #KBestPoly eq 0 then
        if Verbose then printf "Calling PolredbestifyWithRoot..."; t:=Cputime(); end if;
        f, root, KBestIsPolredabs := PolredbestifyWithRoot(R!KPoly);  // iotaK is the isomorphism from Kabs_notbest to Kabs
        if Verbose then printf "%.3o secs\n", Cputime()-t; end if;
        KBest := NumberField(f);
        KBestPoly := Eltseq(f);
    else
        if Verbose then printf "Using specified KBestPoly %o KPoly with IsPolredabs set to %o...", KBestPoly eq KPoly select "eq" else "ne", KBestIsPolredabs; t:=Cputime(); end if;
        KBest := NumberField(R!KBestPoly);
        root := KPoly eq KBestPoly select KBest.1 else Roots(ChangeRing(R!KPoly,KBest))[1][1];
        if Verbose then printf "%.3o secs\n", Cputime()-t; end if;
    end if;
    iota := hom<K->KBest | root>;

    // Write Z in terms of power basis for KBest
    ZBest := Z*Matrix([Eltseq(iota(K.1^i)) : i in [0..Degree(K)-1]]);

    // Verify all is well
    // assert &and[K!Eltseq(Z[m]) eq (iota^-1)(KBest!Eltseq(ZBest[m])) : m in [1..Nrows(Z)]];

    if Verbose then printf "Creating Hecke ring..."; t:=Cputime(); end if;
    n := 0; cnt := 0; mcnt := 1;
    while cnt lt mcnt do
        while cnt lt mcnt and n lt #ZSeq do n+:=1; if not KBest!Eltseq(ZBest[n]) in Rationals() then cnt +:= 1; end if; end while;
        assert cnt eq mcnt;
        try
            O := Order([KBest | KBest!Eltseq(ZBest[i]) : i in [1..n] | IsPrimePower(n) and not KBest!Eltseq(ZBest[n]) in Rationals()]);
            OBasis := Basis(O);
            ZO := ChangeRing(ZBest*Matrix([Eltseq(KBest!b) : b in OBasis])^-1,Integers());
            break;
        catch e
            mcnt +:= 1;
        end try;
    end while;
    if Verbose then printf "%.3o secs, generated by %o non-rational a_n with n up to %o\n", Cputime()-t, mcnt, n; end if;
    if GeneratorBoundOnly then return n; end if;

    if KDisc eq 0 then
        Obest := O;
        discO := Discriminant(O);
        if Verbose then printf "Attempting to determine index of Hecke ring in maximal order..."; t:=Cputime(); end if;
        // Improve O as much as possible to get a divisor of the index
        if KBestIsPolredabs then
            for p in PrimeDivisors(discO) do
                Obest := pMaximalOrder(Obest, p);
            end for;
            KDisc := Discriminant(Obest);
        else
            ps, hard := TrialDivision(discO, 10^7);
            for pdat in ps do  // make p-maximal
                Obest := pMaximalOrder(Obest, pdat[1]);
            end for;
            hard := [ PerfectPowerBase(m) : m in hard];
            notsohard := [ m : m in hard | m le 10^80 or IsProbablePrime(m) ];
            for m in notsohard do
                for p in PrimeDivisors(m) do  // make p-maximal
                    Obest := pMaximalOrder(Obest, p);
                end for;
            end for;
            if #notsohard eq #hard then KDisc := Discriminant(Obest); end if;
        end if;
        _,Oindex := IsSquare(ExactQuotient(Discriminant(O),KDisc eq 0 select Discriminant(Obest) else KDisc));
        if Verbose then printf "%.3o secs, discOK = %o, Oindex = %o\n", Cputime()-t, KDisc, Oindex; end if;
    else
        _,Oindex := IsSquare(ExactQuotient(Discriminant(O),KDisc));
    end if;

    if Verbose then printf "LLL-ing..."; t:=Cputime(); end if;
    prec := Max(1000,10*Round(Log(10,AbsoluteValue(KDisc eq 0 select Discriminant(KBest) else KDisc))));
    retry := 0;
    try 
    // Now compute a small basis.  Note that we need to be sure to use enough precision to guarantee we find a root of unity in Olat
    // (if we don't asserts below will fail)
        Olat, mOlat := MinkowskiLattice(O : Precision := prec);
        _, E := LLL(Olat:Delta:=0.9999);
    catch e
        printf "Warning, error caught in OptimizedOrderBasis, retry %o, increasing precision from %o to %o\n", retry, prec, 2*prec;
        prec := 2*prec;
        try
            Olat, mOlat := MinkowskiLattice(O : Precision := prec);
            _, E := LLL(Olat:Delta:=0.999);
        catch e
            printf "Warning, error caught in OptimizedOrderBasis, retry %o, increasing precision from %o to %o\n", retry, prec, 2*prec;
            prec := 2*prec;
            Olat, mOlat := MinkowskiLattice(O : Precision := prec);
            _, E := LLL(Olat:Delta:=0.999);
        end try;
    end try;
    if Verbose then printf "%.3o secs\n", Cputime()-t; end if;
  
    // Theorem: The shortest vectors of Olat are the roots of unity.
    // Corollary: If 1 is not in a basis of shortest vectors, then 
    //    Olat is spanned additively by roots of unity, so Olat is the maximal
    //    order in a cyclotomic field.
    EinO := [O!Eltseq(e) : e in Rows(E)];
    muEinO := [e : e in EinO | Abs(Norm(mOlat(e))-deg) lt 10^(-Precision(BaseRing(Olat))*9/10) and e notin [1,-1]];
    v := InfinitePlaces(KBest)[1];
    CC := Parent(Evaluate(KBest!1,v));
    pi := Pi(CC);
    muexps := [Roots(PowerRelation(Argument(Evaluate(z,v))/(2*pi),1),Rationals()) : z in muEinO]; // recognize as exp(2*pi*i*mu) with mu in QQ
    muexpshasroots := [i : i in [1..#muexps] | #muexps[i] gt 0];  // pick out ones where a good match was found
    if #muexpshasroots gt 0 then
        muEinO := [muEinO[i] : i in muexpshasroots];
        muexps := [muexps[i][1][1] : i in muexpshasroots];
        m := Lcm([Denominator(k) : k in muexps]);   // candidate denominator
        mus := [z : z in muEinO | z^m eq 1];
        if sub<KBest | ChangeUniverse(mus,KBest)> eq KBest and O eq sub<O | mus> then
            // cyclotomic ring!  Find a combination giving a primitive root of unity to get power basis
            gcd, lincombo := Xgcd([Integers() | m*k : k in muexps]);
            assert gcd eq 1;
            zgen := &*[muEinO[i]^(lincombo[i]) : i in [1..#lincombo]];
            assert O eq sub<O | [zgen^k : k in [0..deg-1]]>;
            E := Matrix(Integers(), [Eltseq(O!zgen^k) : k in [0..deg-1]]);
        end if;
    end if;

    // Order rows by L1 norm then permute cols so diagonal entries are all nonzero (this should ensure the first basis element is 1)
    Erows := Sort([Eltseq(v) : v in Rows(E)],func<a,b|&+[Abs(x):x in a] - &+[Abs(x):x in b]>);
    assert #Erows eq deg;
    E := Matrix(Integers(),Erows);
    for i:= 1 to #Erows do z := [j:j in [i..deg]|E[i][j] ne 0]; if #z gt 0 then SwapColumns(~E,i,Min(z)); end if; end for;
    assert Abs(E[1][1]) eq 1 and &and [E[1][j] eq 0 : j in [2..deg]];
    if E[1][1] eq -1 then E := -E; end if;
  
    Einv := E^-1;
    OLLLBasis := [&+[ E[i][j]*OBasis[j] : j in [1..deg]] : i in [1..deg]];
    ZOE := ZO*Einv;

    // sanity check: make sure seqs match (this can be commented out to improve performance)
    assert &and[KBest!Eltseq(ZBest[m]) eq KBest!&+[ZOE[m][i]*OLLLBasis[i] : i in [1..deg]] : m in [1..Nrows(Z)]];

    OBestBasis := [Eltseq(KBest!c) : c in OLLLBasis];
    assert OBestBasis[1] eq Eltseq(KBest!1);

    if Verbose then printf "OptimizedOrderBasis total time %.3os\n", Cputime()-start; end if;
    return Eltseq(MinimalPolynomial(KBest.1)), OBestBasis, [[r[i]:i in [1..#OBestBasis]]:r in Rows(ZOE)], Integers()!Oindex, KDisc, KBestIsPolredabs, n; 
end intrinsic;


intrinsic CheckOrderGeneratorBound (KPoly::SeqEnum,ZSeq::SeqEnum[SeqEnum],n::RngIntElt) -> BoolElt
{ Given the coefficients of an irreducible monic polynomial f in Q[x] and a sequence of algebraic integers a[] in K := Q[x]/(f(x)) specified in terms of the power basis, and an integer n,
  returns 0 if n is the least integer for which Z[a1,...,an] is equal to the suborder of OK generated by a (requires a to generate an order, not a subring), -1 if n is to small, 1 if too large. }   
    require KPoly[#KPoly] eq 1: "First argument must specify the coefficients of a monic polynomial";
    deg := #KPoly-1;
    require &and[#z eq deg:z in ZSeq]: "Second argument must be a sequence of sequences of less then length of first argument";
    require n ge 1 and n le #ZSeq: "Third argument most be a postiive integer not exceeding the length of the sequence";

    if deg eq 1 or n eq 1 then return deg eq 1 and n eq 1; end if;

    R<x>:=PolynomialRing(Rationals());
    K := NumberField(R!KPoly);
    Z := Matrix(Rationals(),ZSeq);
    try
        O := Order([K|K!Eltseq(Z[i]) : i in [1..n] | not K!Eltseq(Z[n]) in Rationals()]);
        OBasis := Basis(O);
        ZO := ChangeRing(Z*Matrix([Eltseq(K!b) : b in OBasis])^-1,Integers());
    catch e
        return -1;
    end try;
    try
        O := Order([K|K!Eltseq(Z[i]) : i in [1..n-1] | not K!Eltseq(Z[n]) in Rationals()]);
        OBasis := Basis(O);
        ZO := ChangeRing(Z*Matrix([Eltseq(K!b) : b in OBasis])^-1,Integers());
    catch e
        return 0;
    end try;
    return 1;
end intrinsic;

intrinsic NFSeq (KPoly::SeqEnum,  OBasis::SeqEnum[SeqEnum], Seq::SeqEnum[SeqEnum]) -> SeqEnum[FldNumElt]
{ Given poly coefficients defining a number field K, a Z-basis for an order O in O_K, and a sequence of elements of O specified as vectors in this base, returns the corresponding sequence of algebraic integers as elements of K. }
    R<x> := PolynomialRing(Rationals());
    K<a> := NumberField(R!KPoly);
    if #Seq eq 0 then return [K|]; end if;
    return [K|Eltseq(r) : r in Rows(Matrix(Rationals(),Seq)*Matrix(Rationals(),OBasis))];
end intrinsic;

intrinsic NFSeqs (KPoly::SeqEnum,  OBasis::SeqEnum[SeqEnum], Seqs::SeqEnum[SeqEnum[SeqEnum]]) -> SeqEnum[SeqEnum[FldNumElt]]
{ Given poly coefficients defining a number field K, a Z-basis for an order O in O_K, and a list of sequences of elements of O specified as vectors in this base, returns a list of the corresponding sequence of algebraic integers as elements of K. }
    R<x> := PolynomialRing(Rationals());
    K<a> := NumberField(R!KPoly);
    return [#seq eq 0 select [K|] else [K|Eltseq(r) : r in Rows(Matrix(Rationals(),seq)*Matrix(Rationals(),OBasis))]:seq in Seqs];
end intrinsic;

intrinsic NFSeqIsIsomorphic (KPoly1::SeqEnum,Seq1::SeqEnum[SeqEnum], KPoly2::SeqEnum, Seq2::SeqEnum[SeqEnum]) -> BoolElt, SeqEnum[FldRatElt]
{ Given two sequences that both contain a basis for the same number specified in terms of (possibly different) power bases, determine if there is a field isomorphism that maps one sequence to the other.  If returns the image of first power basis generator in the second. }
    require #KPoly1 eq #KPoly2: "Field polynomials must have the same degree";
    require #Seq1 eq #Seq2: "Sequences must have the same length";
    R<x> := PolynomialRing(Rationals());
    require IsIrreducible(R!KPoly1) and IsIrreducible(R!KPoly2): "Field polynomials must be irreducible";
    if not NFPolyIsIsomorphic(KPoly1,KPoly2) then return false,_; end if;  // this can be very slow
    if #Seq1 eq 0 then return true; end if;
    require {#a:a in Seq1} eq {#KPoly1-1} and {#a:a in Seq2} eq {#KPoly2-1}: "Specified sequences do not define Q-vectors of the correct dimension";
    if #KPoly1 eq 2 then if Seq1 eq Seq2 then return true,[1]; else return false,_; end if; end if;
    d := #KPoly1-1;
    V := VectorSpace(Rationals(),d);
    B:=[]; I:=[]; s:=0;
    for i:=1 to #Seq1 do
        if Dimension(sub<V|B,[Seq1[i]]>) gt s then
            Append(~I,i); Append(~B,Seq1[i]);
            s+:=1;
            if s eq d then break; end if;
        end if;
    end for;
    if s lt d then error "Specified sequence does not contain a Q-basis for the specified number field"; end if;
    B1 := Matrix(Rationals(),[Seq1[i]:i in I]);
    B2 := Matrix(Rationals(),[Seq2[i]:i in I]);
    T := B1^-1*B2;
    if Matrix(Rationals(),Seq1)*T ne Matrix(Rationals(),Seq2) then return false,_; end if;
    v := [0:i in [1..d]];  v[2] := 1;
    v := Vector(Rationals(),v) * T;
    K1 := NumberField(R!KPoly1);  K2 := NumberField(R!KPoly2);
    pi := hom<K1->K2|K2!Eltseq(v)>;
    TT := Matrix(Rationals(),[Eltseq(pi(K1.1^n)): n in [0..d-1]]);
    if T ne TT then return false,_; end if;
    return true, Eltseq(v);
end intrinsic;

intrinsic NFSeqIsIsomorphic (KPoly1::RngUPolElt,Seq1::SeqEnum[SeqEnum], KPoly2::RngUPolElt,Seq2::SeqEnum[SeqEnum]) -> BoolElt, SeqEnum[FldRatElt]
{ Given two sequences that both contain a basis for the same number field specified in terms of (possibly different) power bases, determine if there is a field isomorphism that maps one sequence to the other.  If so, returns the image of first power basis generator in the second. }
    return NFSeqIsIsomorphic(Eltseq(KPoly1),Seq1,Eltseq(KPoly2),Seq2);
end intrinsic;        

intrinsic NFSeqIsIsomorphic (Seq1::SeqEnum,Seq2::SeqEnum) -> BoolElt
{ Given two sequences that both contain a basis for the same number field specified in terms of (possibly different) power bases, determine if there is a field isomorphism that maps one sequence to the other. }
    require #Seq1 eq #Seq2: "Sequences must have the same length";
    if #Seq1 eq 0 then return true; end if;
    K1 := Universe(Seq1); if Degree(K1) gt 1 then F, pi := sub<K1|Seq1>; if F ne K1 then Seq1 := [Inverse(pi)(a):a in Seq1]; K1 := F; end if; end if;
    K2 := Universe(Seq2); if Degree(K2) gt 1 then F, pi := sub<K2|Seq2>; if F ne K2 then Seq2 := [Inverse(pi)(a):a in Seq2]; K2 := F; end if; end if;
    if Degree(K1) ne Degree(K2) then return false; end if;
    if Degree(K1) eq 1 then return Seq1 eq Seq2; end if;
    if Type(K1) eq FldCyc then L:=SimpleExtension(K1); b,pi:=IsIsomorphic(K1,L); assert b; Seq1:=[pi(x):x in Seq1]; K1:=L; end if;
    if Type(K2) eq FldCyc then L:=SimpleExtension(K2); b,pi:=IsIsomorphic(K2,L); assert b; Seq2:=[pi(x):x in Seq2]; K2:=L; end if;
    f1 := DefiningPolynomial(K1); f2 := DefiningPolynomial(K2);
    b,v := NFSeqIsIsomorphic(Eltseq(f1), [Eltseq(K1!a):a in Seq1],Eltseq(f2),[Eltseq(K2!a):a in Seq2]);
    // don't bother trying to reconstruct the map, the caller should fix defining polynomials if they want this.
    return b;
end intrinsic;

function CompareCCLists(a,b)
    for i:=1 to #a do
        if Real(a[i]) lt Real(b[i]) then return -1; end if;
        if Real(a[i]) gt Real(b[i]) then return 1; end if;
        if Imaginary(a[i]) lt Imaginary(b[i]) then return -1; end if;
        if Imaginary(a[i]) gt Imaginary(b[i]) then return 1; end if;
    end for;
    return 0;
end function;

// Round real and imaginary parts of complex number z to accuracty of 1/absprec (so values within 1/(2*absprec) will come out the same)
function roundCC(z,absprec)
    return Round(absprec*Real(z))/absprec + Round(absprec*Imaginary(z))/absprec * Parent(z).1;
end function;

intrinsic LabelEmbeddings (a::SeqEnum[FldNumElt], L::SeqEnum[RngIntElt]: Precision:=100) -> SeqEnum[SeqEnum[RngIntElt]]
{ Given a sequence of elements a of number field K and a sequence of integers n indexed by embeddings of K, returns a list of unique labels for the embeddings of K
  in which each label is a pair [n,i] with i=1,2,3,.. chosen according to the lex ordering of the embeddings of a, where complex numbers are lex ordered by read and imagainary parts. }
    require #L eq Degree(Universe(a)): "List L must have length equal to the degree of the number field in which the sequence a lies.";
    require #{Multiplicity(Multiset(L),n):n in L} eq 1: "Each distinct entry in L must occur with the same multiplicity.";
    d := #L;  m := ExactQuotient(d,#Set(L));
    if m eq 1 then return [[L[i],1]:i in [1..d]]; end if;
    S := [<Conjugates(n:Precision:=Precision)[1]>:n in L];
    n := 0;
    while #Set(S) lt d do
        n +:= 1;
        if a[n] eq 0 or Degree(MinimalPolynomial(a[n])) eq 1 then continue; end if;
        c := Conjugates(a[n]:Precision:=Precision+10);
        c := [roundCC(x,10^(Precision)):x in c];
        if #Set(c) ne Degree(MinimalPolynomial(a[n])) or #Set(Multiplicities(Multiset(c))) ne 1 then Sprintf("Insufficient precision %o specified in function LabelEmbeddings, you need to increase it.", Precision); end if;
        S := [Append(S[i],c[i]):i in [1..d]];
    end while;
    S,s := Sort(S,func<a,b|CompareCCLists(a,b)>);
    T := [i:i in [1..d]]^s;
    LL := [*[L[i],0]:i in [1..#L]*];
    n := 1;
    for i:= 1 to d do
        if n gt m then n:=1; end if;
        j := T[i];
        LL[j] := [L[j],n];
        n +:= 1;
    end for;
    return LL;
end intrinsic;


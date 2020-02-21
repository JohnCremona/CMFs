// depends on utils.m

intrinsic NFDiscriminant (f::RngUPolElt) -> RngIntElt
{ Given an irreducible polynomial in Q[x] returns the discriminant of the number field it defines. }
    return Integers()!Discriminant(RingOfIntegers(NumberField(f)));
end intrinsic;

intrinsic NFDiscriminant (f::SeqEnum) -> RngIntElt
{ Given an irreducible polynomial in Q[x] returns the discriminant of the number field it defines. }
    return Integers()!Discriminant(RingOfIntegers(NumberField(PolynomialRing(Rationals())!f)));
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

intrinsic Resolvents (f::RngUPolElt:d:=0,Galois:=false,Proof:=true) -> SeqEnum[RngUPolElt]
{ Returns a list of resolvents of the polynomial f, either of the specified degree d, or of all degrees up to the degree of f.  If Galois is set, restricts to Galois resolvents. }
    require Degree(f) ge 1: "Polynomial must be nonconstant";
	G,r,S := GaloisGroup(f);  if Proof then assert GaloisProof(f,S); end if;
	subs := [H`subgroup : H in (d gt 0 select Subgroups(G:IndexEqual:=d) else Subgroups(G:IndexLimit:=Degree(f)))|not Galois or IsNormal(G,H`subgroup)];
	return [Parent(f)!GaloisSubgroup(S,H) : H in subs];
end intrinsic;

intrinsic Resolvents (f::SeqEnum:d:=0,Galois:=false,Proof:=true) -> SeqEnum[SeqEnum]
{ Returns a list of resolvents of the polynomial f, either of the specified degree d, or of all degrees up to the degree of f.  If Normal is set, restricts to Galois resolvents. }
	return [Eltseq(g):g in Resolvents(PolynomialRing(Rationals())!f:d:=d,Galois:=Galois,Proof:=Proof)];
end intrinsic;

intrinsic CentralResolvent (f::RngUPolElt:Proof:=true) -> SeqEnum[RngUPolElt]
{ Returns a defining polynomial for the subfield of the splitting field of the specified polynomial fixed by the center of its Galois group.  }
    require Degree(f) ge 1: "Polynomial must be nonconstant";
	G,r,S := GaloisGroup(f);  if Proof then assert GaloisProof(f,S); end if;
	return Parent(f)!GaloisSubgroup(S,Center(G));
end intrinsic;

intrinsic CentralResolvent (f::SeqEnum:Proof:=true) -> SeqEnum[SeqEnum]
{ Returns a defining polynomial for the subfield of the splitting field of the specified polynomial fixed by the center of its Galois group.  }
	return CentralResolvent(PolynomialRing(Rationals())!f:Proof:=Proof);
end intrinsic;

intrinsic Siblings (f::RngUPolElt:d:=0,Proof:=true) -> SeqEnum[RngUPolElt]
{ Returns a list of polynomials with the same splitting field as f, either of the specified degree d, or of any degree up to the degree of f.}
    require Degree(f) ge 1: "Polynomial must be nonconstant";
	G,r,S := GaloisGroup(f);  if Proof then assert IsMonic(f) and IsIrreducible(f) and GaloisProof(f,S); end if;
	subs := Sort([H`subgroup : H in (d gt 0 select Subgroups(G:IndexEqual:=d) else Subgroups(G:IndexLimit:=Degree(f))) | #Core(G,H`subgroup) eq 1],func<a,b|#b-#a>);
	return [Parent(f)!GaloisSubgroup(S,H) : H in subs];
end intrinsic;

intrinsic Siblings (f::SeqEnum:d:=0,Proof:=true) -> SeqEnum[SeqEnum]
{ Returns a list of polynomials with the same splitting field as f, either of the specified degree d, or of any degree up to the degree of f.}
	return [Eltseq(g):g in Siblings(PolynomialRing(Universe(f))!f:d:=d,Proof:=Proof)];
end intrinsic;

intrinsic MinimalDegreeSiblings (f::RngUPolElt) -> SeqEnum[RngUPolElt]
{ Returns a list of polynomials of minimal degree that have the same splitting field as f.}
    require Degree(f) ge 1: "Polynomial must be nonconstant";
    G,r,S := GaloisGroup(f);  if IsMonic(f) and IsIrreducible(f) then assert GaloisProof(f,S); end if;
    subs := Sort([H`subgroup : H in Subgroups(G:IndexLimit:=Degree(f)) | #Core(G,H`subgroup) eq 1],func<a,b|#b-#a>);
    subs := [H : H in subs | #H eq #subs[1]];
    return [Parent(f)!GaloisSubgroup(S,H) : H in subs];
end intrinsic;

intrinsic MinimalDegreeSiblings (f::SeqEnum) -> SeqEnum[SeqEnum]
{ Returns a list of polynomials of minimal degree that have the same splitting field as f.}
    return [Eltseq(g):g in MinimalDegreeSiblings(PolynomialRing(Universe(f))!f)];
end intrinsic;

intrinsic MinimalSibling (f::RngUPolElt:RamificationBound:=0,OnlyPolredbest:=false) -> RngUPolElt
{ Returns Polredabs polynomial of minimal degree polynomial whose splitting field is the same as f with minimal number of decimal digits (ties broken by L1-norm then lex).}
    require Degree(f) ge 1: "Polynomial must be nonconstant";
    require BaseRing(f) eq Rationals() or BaseRing(f) eq Integers(): "Polynomial must be defined over Q or Z";
    if Degree(f) eq 1 then return Parent(f)![1,0]; end if;
    sibs := MinimalDegreeSiblings(f);
    P := RamificationBound gt 0 select Sort([r[1]:r in TrialDivision(GCD([Integers()!Discriminant(g):g in sibs]),RamificationBound) | r[1] le RamificationBound]) else [];
    if OnlyPolredbest then
        if #sibs eq 1 then return polredbest(sibs[1]:DiscFactors:=P); end if;
        sibs := [polredbest(g:DiscFactors:=P):g in sibs];
    else
        if #sibs eq 1 then return polredabs(sibs[1]:DiscFactors:=P); end if;
        sibs := [polredabs(g:DiscFactors:=P):g in sibs];
    end if;
    bitsize := func<f|&+[Ceiling(Log(10,Abs(c)+0.1)):c in Coefficients(f)|c ne 0]>;
    l1norm := func<f|Max([Abs(c):c in Coefficients(f)])>;
    sibs := Sort(sibs,func<g,h|bb ne 0 select bb else ll ne 0 select ll else (Eltseq(g) le Eltseq(h) select -1 else 1) where bb:=bitsize(g)-bitsize(h) where ll:=l1norm(g)-l1norm(h)>);
    return sibs[1];
end intrinsic;

intrinsic MinimalSibling (f::SeqEnum:RamificationBound:=0,OnlyPolredbest:=false) -> SeqEnum
{ Returns Polredabs polynomial of minimal degree defining number field of minimal discriminant with minimal L2-norm whose Galois closure is the splitting field as f (ties are broken lexicographically).}
    return Eltseq(MinimalSibling(PolynomialRing(Rationals())!f:RamificationBound:=RamificationBound,OnlyPolredbest:=OnlyPolredbest));
end intrinsic;

intrinsic MinimalCentralSibling (f::RngUPolElt:RamificationBound:=0,OnlyPolredbest:=false) -> RngUPolElt
{ Given an irreducible polynomial f in Q[x] returns an irreducible polynomial g of minimal degree and minimal |disc(Q[x]/(g))|) such that the splitting field of g is the fixed field of the center of the Galois group of f. }
    require Degree(f) ge 1: "Polynomial must be nonconstant";
    require BaseRing(f) eq Rationals() or BaseRing(f) eq Integers(): "Polynomial must be defined over Q or Z";
    G,r,S := GaloisGroup(f);  assert GaloisProof(f,S);
    g := Parent(f)!GaloisSubgroup(S,Center(G));
    return MinimalSibling(g:RamificationBound:=RamificationBound,OnlyPolredbest:=OnlyPolredbest);
end intrinsic;

intrinsic MinimalCentralSibling (f::SeqEnum:RamificationBound:=0,OnlyPolredbest:=false) -> SeqEnum
{ Given an irreducible polynomial f in Q[x] returns an irreducible polynomial g of minimal degree and minimal |disc(Q[x]/(g))|) such that the splitting field of g is the fixed field of the center of the Galois group of f. }
    return Eltseq(MinimalCentralSibling(PolynomialRing(Universe(f))!f:RamificationBound:=RamificationBound,OnlyPolredbest:=OnlyPolredbest));
end intrinsic;

intrinsic IsSibling (f::RngUPolElt,g::RngUPolElt:Proof:=true) -> BoolElt
{ Returns true if the number fields defined by the specified polynomials (which should be irreducible) are siblings. }
	S := Siblings(g:d:=Degree(g),Proof:=Proof);
	if #S eq 0 then return false; end if;
	K := NumberField(g);
	return &or[IsIsomorphic(K,NumberField(h)):h in S];
end intrinsic;

intrinsic IsSibling (f::SeqEnum,g::SeqEnum:Proof:=true) -> BoolElt
{ Returns true if the number fields defined by the specified polynomials (which should be irreducible) are siblings. }
	R<x> := PolynomialRing(Rationals());
	return IsSibling(R!f,R!g:Proof:=Proof);
end intrinsic;

intrinsic NumberField (K::FldRat) -> FldNum
{ Override Magma version of this function (which does not return a number field), so that IsNumberField(NumberField(Rationals())) returns true, not false. }
    return RationalsAsNumberField();
end intrinsic;

intrinsic NumberField (Z::RngInt) -> FldNum
{ Override Magma version of this function (which does not return a number field), so that IsNumberField(NumberField(Integers())) returns true, not false. }
    return RationalsAsNumberField();
end intrinsic;

intrinsic TorsionGenerator (K::FldNum) -> FldNumElt, RngIntElt
{ returns a generator for the torsion subgroup of the multiplicative group of K along with its order. }
    // handle obviously cyclotomic fields quickly (but don't call IsCyclotomic, it is too slow)
    b,n := IsCyclotomicPolynomial(DefiningPolynomial(K));
    if b then if IsEven(n) then return K.1,n; else return -K.1,2*n; end if; end if;
    U,pi := TorsionUnitGroup(K);
    return pi(U.1), #U;
end intrinsic;

intrinsic AmbientField (K1::FldNum,K2::FldNum) -> FldNum, Map, Map
{ Given number fields K1 and K2 returns a number field K and embeddings pi1:K1->K and pi2:K2->K.  Tries to handle easy cases quickly. }
    if Degree(K1) eq 1 and Degree(K2) eq 1 then K := RationalsAsNumberField(); pi1 := hom<K1->K|1>; pi2 := hom<K1->K|1>; return K,pi1,pi2; end if;
    if Degree(K1) eq 1 then K := K2; pi1 := hom<K1->K|1>; pi2 := hom<K2->K|K.1>; return K,pi1,pi2; end if;
    if Degree(K2) eq 1 then K := K1; pi2 := hom<K2->K|1>; pi1 := hom<K1->K|K.1>; return K,pi1,pi2; end if;
    R<x> := PolynomialRing(Rationals());
    f1 := R!DefiningPolynomial(K1); f2 := R!DefiningPolynomial(K2);
    if f1 eq f2 then K := K1;  pi1 := hom<K1->K|K.1>; pi2 := hom<K2->K|K.1>; return K, pi1, pi2; end if;
    if Degree(f1) eq Degree(f2) and f1 eq Evaluate(f2,-x) then K := K1;  pi1 := hom<K1->K|K.1>; pi2 := hom<K2->K|-K.1>; return K, pi1, pi2; end if;
    if Degree(f1) eq 2*Degree(f2) and f1 eq Evaluate(f2,x^2) then K := K1;  pi1 := hom<K1->K|K.1>; pi2 := hom<K2->K|K.1^2>; return K, pi1, pi2; end if;
    if Degree(f2) eq 2*Degree(f1) and f2 eq Evaluate(f1,x^2) then K := K2;  pi2 := hom<K2->K|K.1>; pi1 := hom<K1->K|K.1^2>; return K, pi1, pi2; end if;
    // If one of K1,K2 is a subfield of the other it may be much faster to use IsSubfield, but it can also be *dramatically* slower, so we don't
    K := CompositeFields(K1,K2)[1]; b, pi1 := IsSubfield(K1,K); assert b; b, pi2 := IsSubfield(K2,K); assert b;
    return K, pi1, pi2;
end intrinsic;

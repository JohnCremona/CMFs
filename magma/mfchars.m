// Dependencies
// Attach("chars.m")

// References to Ribet below refer to "Twists of modular forms and endomorphisms of abelian varieties" https://math.berkeley.edu/~ribet/Articles/annalen_253.pdf
// But note that we allow arbitrary weight and consider inner twists of CM forms, whereas Ribet always assumes k=2 and no-CM, so we need to be careful

intrinsic RealCyclotomicPolynomial(n::RngIntElt) -> RngUPolElt[RatFldElt]
{ Returns a defining polynomial for the real cyclotomic field Q(zeta_n)^+. }
    F:=CyclotomicField(n);
    return MinimalPolynomial(F.1+1/F.1);
end intrinsic;

intrinsic RealCyclotomicField(n::RngIntElt) -> NumFld
{ Returns the real cyclotomic field Q(zeta_n)^+. }
    return NumberField(RealCyclotomicPolynomial(n));
end intrinsic;

intrinsic  EmbedCharacterField (chi::GrpDrchElt,k::RngIntElt,a::SeqEnum[FldNumElt]) -> Map
{ Computes a Hecke-compatible embeding of Q(chi) into the coefficient field Q(f) of a weight k eigenform f of character chi with specified Fourier coefficients (NB: an error may occur if not enough coefficients are provided). }
    require k gt 0: "Weight must be a positive integer";
    K := Universe(a);
    if Degree(chi) eq 1 then return hom<Rationals()->K|>; end if;
    N := Modulus(chi); e := Order(chi); F:=CyclotomicField(e);
    b,m := IsCyclotomicPolynomial(DefiningPolynomial(K));
    if b then
        if IsDivisibleBy(m,e) then z := K.1^ExactQuotient(m,e); else assert IsOdd(m) and IsDivisibleBy(2*m,e); z := (-K.1)^ExactQuotient(2*m,e); end if;
    else
        z := Roots(ChangeRing(DefiningPolynomial(F),K))[1][1];
    end if;
    assert z^e eq 1;
    T := [r:r in [1..e-1]|GCD(r,e) eq 1];
    for n:= 2 to Floor(Sqrt(#a)) do
        if GCD(N,n) ne 1 then continue; end if;
        T := [r:r in T|a[n]^2 eq &+[d^(k-1)*rho(chi(d))*a[ExactQuotient(n,d)^2]:d in Divisors(n)] where rho:=hom<F->K|z^r>];
        assert #T gt 0;
        if #T eq 1 then break; end if;
    end for;
    assert #T eq 1; // This may fail if not enough coefficients were provided
    return hom<F->K|z^T[1]>;
end intrinsic;

intrinsic EmbeddedCharacterValuesOnUnitGenerators (chi::GrpDrchElt,k::RngIntElt,a::SeqEnum[FldNumElt]) -> SeqEnum[FldNumElt]
{ Given a list of Fourier coefficients for a weight k eigenform f of level N and character chi returns a list of values of chi on standard unit generators for (Z/NZ)* as elements of the coefficient field Q(f). }
    rho := EmbedCharacterField (chi,k,a);
    return [Universe(a)|rho(z):z in ValuesOnUnitGenerators(chi)];
end intrinsic;

intrinsic EmbeddedCharacter (chi::GrpDrchElt,k::RngIntElt,a::SeqEnum[FldNumElt]) -> Map
{ Given a Dirichlet character chi and a list of Fourier coeffiecients of a weight k eigenform f of character chi returns a map xi:Z -> Q(f) giving the values of chi in the coefficient field Q(f). }
    return CharacterFromValues(Modulus(chi),UnitGenerators(chi),EmbeddedCharacterValuesOnUnitGenerators(chi,k,a));
end intrinsic;

intrinsic UnEmbeddedCharacter (xi::Map, N::RngIntElt) -> GrpDrchElt, Map
{ Given a map xi:Z -> K specifying a Dirichlet character of modulus N with values in a number field K returns a Dirichlet charater chi and a homomorphism rho:Q(chi)->K such that rho(chi)=xi. }
    K := Codomain(xi);
    e := Order(xi,N);
    if e eq 1 then return DirichletGroup(N)!1,hom<Rationals()->K|>; end if;
    U := UnitGenerators(DirichletGroup(N)); v := [xi(u):u in U];
    if e eq 2 then for chi in Elements(DirichletGroup(N)) do if Order(chi) eq 2 and [chi(u) : u in U] eq v then return chi,hom<Rationals()->K|>; end if; end for; assert false; end if;
    // find n for wich xi(n) has order e (such an n exists because the image of xi is cyclic)
    d:=[e div p:p in PrimeDivisors(e)];
    n:=2; while n lt N do if GCD(N,n) eq 1 then z := xi(n); if &and [z^a ne 1:a in d] then break; end if; end if; n +:= 1; end while; assert n ne N;
    F := CyclotomicField(e);
    rho := hom<F->K|xi(n)>;
    for chi in Elements(DirichletGroup(N,F)) do if Order(chi) eq e and [rho(chi(u)) : u in U] eq v then return chi,rho; end if; end for; assert false;
end intrinsic;

// One can do better than this for trivial character, N square free, and when cond(chi) is a proper divisor of N, see Stein 9.19,9.21,9.22,
// but this bound (due to Buzzard) works for all spaces M_k(N,chi) and is best possible in some cases, see Stein 9.20
intrinsic SturmBound (N::RngIntElt, k::RngIntElt) -> RngIntElt
{ Sturm bound for space of modular forms of level N weight k and any character. }
    require N ge 1 and k ge 1: "Level N and weight k must be positive integers";
    m := Index(Gamma0(N));
    return Integers()!Floor(k*m/12);
end intrinsic;

// [obsolete] Use Shimura 3.6.4 to get Sturm bound for twist of form of character chi by a character phi
// Use Lemma 1.4 in  Booker, Min, Strombergsson https://arxiv.org/pdf/1803.06016.pdf, Lemma 12.2.1 in CMF paper
// No longer used -- per Lemma 12.2.8 it suffices to check to the max of the Sturm bound and the largest Hecke cutter prime
intrinsic TwistSturmBound (N::RngIntElt, k::RngIntElt, chi::GrpDrchElt, psi::GrpDrchElt) -> RngIntElt
{ Sturm bound for space known to contain twist of form of level N weight k character chi by character psi. }
    require N ge 1 and k ge 1: "Level N and weight k must be positive integers";
//    return SturmBound(LCM([N,Conductor(phi)^2,Conductor(phi)*Conductor(chi)]),k);
    return SturmBound(LCM([N,Conductor(psi)*Conductor(psi*chi)]),k);
end intrinsic;

intrinsic SelfTwistCandidates (a::SeqEnum, N::RngIntElt, k::RngIntElt) -> SeqEnum[RngIntElt]
{ Given sequence of coefficients a=[a_1,a_2,...] of a newform of level N and weight k, returns a list of primitive characters of conductor D dividing N for which it is possible that the newform admits a self-twist by Kronecker(D,*); all such characters be odd if k > 1. }
    D := [**];
    P := PrimesInInterval(1,#a);
    for chi in [x: x in Elements(DirichletGroup(N)) | Order(x) eq 2 and (k eq 1 or IsOdd(x))] do
        if &and[a[p] eq 0 : p in P | chi(p) eq -1] then Append(~D,DirichletGroup(Conductor(chi))!chi); end if;
    end for;
    return D;
end intrinsic;

intrinsic SelfTwists (a::SeqEnum, S::ModSym: TraceHint:=[], pBound:=0) -> SeqEnum[RngIntElt]
{ Given a (possibly empty) prefix of the q-expansion of an eigenform f for a space of modular symbols S returns a list of fundamental discriminants D for which f admits a self-twist by Kronecker(D,*).  Currently requires k >= 2, in which case this list is either empty or contains a single negative discriminant.
  Checks primes up to greater of #a, Sturm bound, and pBound (set pBound to the largest Hecke cutter prime to get a provably correct result). }
    N := Level(S);  k := Weight(S);  chi := DirichletCharacter(S);
    assert k ge 2; // this ensures only one self twist (and it must be by an odd quadratic character)
    if Order(chi) eq 1 and IsSquarefree(N) then return [Integers()|]; end if;  // apply Ribet Thm. 3.9 and Cor 3.10 if character is trivial
    // If TraceHint is specified, try to use it to rule out self twists: if trace(a_p)!=0 then a_p!=0 and we know chi(p)=1 (without computing a_p)
    if #TraceHint gt 0 then
        DT := SelfTwistCandidates(TraceHint,N,k);
        if #DT eq 0 then return [Integers()|]; end if;
    else
        DT := [**];
    end if;
    if #a lt 7 then F := Eigenform(S,8); a:=[Coefficient(F,n) : n in [1..7]]; end if;
    DC := SelfTwistCandidates(a,N,k);
    // Only keep candidates that also worked for the trace hint, if one was given
    D := #DT gt 0 select [*psi:psi in DC|#[i:i in [1..#DT]|DT[i] eq psi] gt 0*] else DC;
    if #D eq 0 then return [Integers()|],true; end if;
    while #D gt 1 do 
        F := Eigenform(S,#a+1);
        a := [Coefficient(F,n) : n in [1..2*#a]];
        DC := SelfTwistCandidates(a,N,k);
        D := #DT gt 0 select [*psi:psi in DC|#[i:i in [1..#DT]|DT[i] eq psi] gt 0*] else DC;
    end while;
    if #D eq 0 then return [Integers()|]; end if;
    psi := D[1];
    B := Max([#a,SturmBound(N,k),pBound]);
    P := PrimesInInterval(1,B);
    s := Cputime();
    if B le #a then 
        for p in P do if psi(p) eq -1 and a[p] ne 0 then return [Integers()|]; end if; end for;
        return [Parity(psi)*Conductor(psi)];
    end if;
    if B gt 1000 then
        printf "Computing a_p for p <= %o to check if dimension %o eigenform of level %o, weight %o, chi-conductor %o admits self-twists by %o...\n", B, QDimension(S), N, k, Conductor(chi), D;
        s := Cputime();
    end if;
    F := Eigenform(S,P[#P]+1);
    if B gt 1000 then printf "Took %.3o seconds to compute %o eigenform coefficients\n", Cputime()-s, B; end if;
    for p in P do if psi(p) eq -1 and Coefficient(F,p) ne 0 then return [Integers()|],true; end if; end for;
    return [Sign(psi)*Conductor(psi)];
end intrinsic;

intrinsic TwistingCharacters (x1::GrpDrchElt,x2::GrpDrchElt) -> List
{ Given Dirichlet characters x1 and x2 returns a list of Dirichlet characters chi for which x1*chi^2 = x2.  The modulus of chi will be the LCM M of the moduli of x1 and x2 if both have odd conductor, otherwise it will be of modulus 8*M. }
    N := LCM(Modulus(x1),Modulus(x2));
    if IsEven(Conductor(x1)) or IsEven(Conductor(x2)) then N := LCM(N,8); end if;
    x1 := FullDirichletGroup(N)!x1; x2 := FullDirichletGroup(N)!x2;
    chi2 := x2 / x1;
    if IsOdd(Order(chi2)) then
        chi := Sqrt(chi2);
    else
        // Deal with case Magma doesn't know how to handle
        g := Generators(Parent(chi2));
        n := [Order(x):x in g];
        e := ElementToSequence(chi2);
        assert #e eq #g and &*[g[i]^e[i]:i in [1..#g]] eq chi2;
        if #[i:i in [1..#g]|IsEven(n[i]) and IsOdd(e[i])] gt 0 then return [**]; end if; // no square root
        chi := &*[g[i]^(IsEven(e[i]) select e[i] div 2 else ((e[i]*InverseMod(2,n[i])) mod n[i])):i in [1..#g]];
    end if;
    return [*MinimalBaseRingCharacter(AssociatedPrimitiveCharacter(x*chi)):x in Elements(DirichletGroup(N))*]; // 2-torsion Dirichlet chars are precisely the rational ones (which is what DirichletGroup returns)
end intrinsic;

intrinsic InnerTwists (a::SeqEnum, chi::GrpDrchElt, k::RngIntElt) -> List, RngIntElt
{ Given a list of coffieicnts of the q-expansion of an eigenform f of character chi and weight k returns a list Dirichlet characters psi for which f*psi is conjugate to f, provided #a exceeds the Sturm bound and the largest Hecke cutter prime, result is rigorous.  Note: assumes Parent(a) = Q(f). }
    N := Modulus(chi);
    K := Universe(a);
    if Degree(K) eq 1 then return [**]; end if;
    if Order(chi) eq 1 and IsSquarefree(N) then return [**]; end if;  // we can apply Ribet Thm. 3.9 and Cor 3.10 if chi is trivial
    // Ribet Prop. 3.2 holds in general: if f has an inner twist by phi then phi must take values in Q(chi) \subseteq Q(f)
    // In fact, more is true: if chi takes nonzero values in <zeta_m> then phi takes values in <+/-zeta_m>
    // We use cond(psi)cond(chi*psi) | N, per Lemma 1.4 of Booker, Min, Strombergsson https://arxiv.org/pdf/1803.06016.pdf
    // which is also Theorem 12.2.5 in CMF paper
    X := &cat [[* psi : psi in TwistingCharacters(chi,gchi) | IsDivisibleBy(N,Conductor(psi)*Conductor(chi*psi)) and IsDivisibleBy(LCM(2,Order(chi)),Order(psi)) and Conductor(psi) gt 1 *] : gchi in Conjugates(chi)];
    if #X eq 0 then return [**]; end if;
    rho := EmbedCharacterField(chi,k,a);
    n := 0;
    P := [p: p in PrimesInInterval(1,#a) | GCD(N,p) eq 1 and a[p] ne 0];
    for p in P do
        f := MinimalPolynomial(a[p]);
        X := [* psi : psi in X | MinimalPolynomial(rho(psi(p))*a[p]) eq f *];
        if #X eq 0 then return [**]; end if;
        n +:= 1;
        if n eq 10 then break; end if;  // arbitrary cutoff, doesn't effect correctness only performance
    end for;
    A := Remove(Automorphisms(K),1);
    Y := [**];
    for psi in X do
        B := A;
        for p in P do B := [s : s in B | s(a[p]) eq rho(psi(p))*a[p]]; if #B le 1 then break; end if; end for;
        if #B eq 0 then continue; end if;
        assert #B eq 1;
        s := B[1];
        if #[p : p in P | s(a[p]) eq rho(psi(p))*a[p]] eq #P then Append(~Y,psi); end if;
    end for;
    if #Y eq 0 then return [**], #a; end if;
    return [* MinimalBaseRingCharacter(psi) : psi in Y *];
end intrinsic;


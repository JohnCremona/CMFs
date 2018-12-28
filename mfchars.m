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

intrinsic SturmBound (N::RngIntElt, k::RngIntElt) -> RngIntElt
{ Sturm bound for space of modular forms of level N weight k (and any character). }
    require N ge 1 and k ge 1: "Level N and weight k must be positive integers";
    m := Index(Gamma0(N));
    return Integers()!Floor(m*k/12-(m-1)/N);
end intrinsic;

// Use Shimura 3.6.4 to get Sturm bound for twist of form of character chi by a character phi
intrinsic TwistSturmBound (N::RngIntElt, k::RngIntElt, chi::GrpDrchElt, phi::GrpDrchElt) -> RngIntElt
{ Sturm bound for space known to contain twist of form of level N weight k character chi by character phi. }
    require N ge 1 and k ge 1: "Level N and weight k must be positive integers";
    return SturmBound(LCM([N,Conductor(phi)^2,Conductor(phi)*Conductor(chi)]),k);
end intrinsic;

// Use Shimura 3.6.4 to get Sturm bound for twist of form of character chi by a character phi
intrinsic TwistSturmBound (N::RngIntElt, k::RngIntElt, cchi::RngIntElt, cphi::RngIntElt) -> RngIntElt
{ Sturm bound for space known to contain twist of form of level N weight k character chi by character phi. }
    require N ge 1 and k ge 1 and cchi ge 1 and cphi ge 1: "Level N, weight k, and conductors of chi and phi must be positive integers";
    return SturmBound(LCM([N,cphi^2,cchi*cphi]),k);
end intrinsic;

intrinsic SelfTwistCandidates (a::SeqEnum, N::RngIntElt, k::RngIntElt) -> SeqEnum[RngIntElt]
{ Given sequence of coefficients a=[a_1,a_2,...] of a newform of level N and weight k, returns a list of integers D dividing N for which it is possible that the newform admits a self-twist by Kronecker(D,*); all such D will be negative if k > 1. }
    D := [Integers()|];
    P := PrimesInInterval(1,#a);
    for chi in [x: x in Elements(DirichletGroup(N)) | Order(x) eq 2 and (k eq 1 or IsOdd(x))] do
        sign := IsOdd(chi) select -1 else 1;
        if &and[a[p] eq 0 : p in P | chi(p) eq -1] then Append(~D,sign*Conductor(chi)); end if;
    end for;
    return D;
end intrinsic;

intrinsic SelfTwists (a::SeqEnum, S::ModSym) -> SeqEnum[RngIntElt]
{ Given a (possibly empty) prefix of the q-expansion of an eigenform f for a space of modular symbols S returns a list of fundamental discriminants D for which f admits a self-twist by Kronecker(D,*).  In weight k >= 2 this list is either empty or contains a single negative discriminant.  }
    N := Level(S);  k := Weight(S);  chi := DirichletCharacter(S);
    assert k ge 2; // this ensures only one self twist (and it must be by a negative quadratic character)
    if Order(chi) eq 1 and IsSquarefree(N) then return [Integers()|]; end if;  // apply Ribet Thm. 3.9 and Cor 3.10 if character is trivial
    if #a le 10 then F := Eigenform(S,101); a:=[Coefficient(F,n) : n in [1..100]]; end if;
    D := SelfTwistCandidates(a,N,k);
    if #D eq 0 then return [Integers()|]; end if;
    while #D gt 1 do 
        F := Eigenform(S,#a+1);
        a := [Coefficient(F,n) : n in [1..2*#a]];
        D := SelfTwistCandidates(a,N,k);
    end while;
    if #D eq 0 then return [Integers()|]; end if;
    D := D[1];
    B := TwistSturmBound (N,k,Abs(D),Conductor(chi));
    P := PrimesInInterval(1,B);
    s := Cputime();
    if B le #a then 
        for p in P do if KroneckerSymbol(D,p) eq -1 and a[p] ne 0 then return []; end if; end for;
        return [D];
    end if;
    if B gt 1000 then
        printf "Computing a_p for p <= %o to check if dimension %o eigenform of level %o, weight %o, chi-conductor %o has CM by %o...\n", B, Dimension(S), N, k, Conductor(chi), D;
        s := Cputime();
    end if;
    F := Eigenform(S,P[#P]+1);
    if B gt 1000 then printf "Took %.3o seconds to compute %o eigenform coefficients\n", Cputime()-s, B; end if;
    for p in P do if KroneckerSymbol(D,p) eq -1 and Coefficient(F,p) ne 0 then return [Integers()|]; end if; end for;
    return [D];
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
{ Given a list of coffieicnts of the q-expansion of an eigenform f of character chi and weight k returns a list Dirichlet characters phi for which f*phi is conjugate to f; also returns a corresponding list of integers n such that checking a_p  for p <= n suffices to give a rigorous result (so if #a >= n, result is rigorous and otherwise not).  Note: assumes Parent(a) = Q(f). }
    N := Modulus(chi);
    K := Universe(a);
    if Degree(K) eq 1 then return [**], 0; end if;
    if Order(chi) eq 1 and IsSquarefree(N) then return [**], 0; end if;  // we can apply Ribet Thm. 3.9 and Cor 3.10 if chi is trivial
    // Ribet Prop. 3.2 holds in general: if f has an inner twist by phi then phi must take values in Q(chi) \subseteq Q(f)
    // In fact, more is true: if chi takes nonzero values in <zeta_m> then phi takes values in <+/-zeta_m>
    X := &cat [[* phi : phi in TwistingCharacters(chi,gchi) | IsDivisibleBy(LCM(2,Order(chi)),Order(phi)) and Conductor(phi) gt 1 *] : gchi in Conjugates(chi)];
    if #X eq 0 then return [**], 0; end if;
    rho := EmbedCharacterField(chi,k,a);
    n := 0;
    P := [p: p in PrimesInInterval(1,#a) | GCD(N,p) eq 1 and a[p] ne 0];
    for p in P do
        f := MinimalPolynomial(a[p]);
        X := [* phi : phi in X | MinimalPolynomial(rho(phi(p))*a[p]) eq f *];
        if #X eq 0 then return [**], p; end if;
        n +:= 1;
        if n eq 10 then break; end if;  // arbitrary cutoff, doesn't effect correctness only performance
    end for;
    A := Remove(Automorphisms(K),1);
    Y := [**];
    for phi in X do
        B := A;
        for p in P do B := [s : s in B | s(a[p]) eq rho(phi(p))*a[p]]; if #B le 1 then break; end if; end for;
        if #B eq 0 then continue; end if;
        assert #B eq 1;
        s := B[1];
        if #[p : p in P | s(a[p]) eq rho(phi(p))*a[p]] eq #P then Append(~Y,phi); end if;
    end for;
    if #Y eq 0 then return [**], #a; end if;
    M := [TwistSturmBound(N,k,chi,phi) : phi in Y];
    return [* MinimalBaseRingCharacter(chi) : chi in Y *], M;
end intrinsic;


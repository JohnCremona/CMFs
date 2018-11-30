Attach("chars.m");

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

intrinsic TwistingCharacters (x1::GrpDrchElt,x2::GrpDrchElt) -> SeqEnum[GrpDrchElt]
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
        if #[i:i in [1..#g]|IsEven(n[i]) and IsOdd(e[i])] gt 0 then return []; end if; // no square root
        chi := &*[g[i]^(IsEven(e[i]) select e[i] div 2 else ((e[i]*InverseMod(2,n[i])) mod n[i])):i in [1..#g]];
    end if;
    return [*MinimalBaseRingCharacter(x*chi):x in Elements(DirichletGroup(N))*];
end intrinsic;

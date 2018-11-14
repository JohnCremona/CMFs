Attach("chars.m");

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
{ Given a Dirichlet character chi and a list of Fourier coeffiecients of a weight k eigenform f of character chi returns a map Z -> Q(f) giving the values of chi in the coefficient field Q(f). }
    return CharacterFromValues(Modulus(chi),UnitGenerators(chi),EmbeddedCharacterValuesOnUnitGenerators(chi,k,a));
end intrinsic;

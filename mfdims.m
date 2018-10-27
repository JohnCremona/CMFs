function prod(a) return #a gt 0 select &*a else 1; end function;

// Function defined on page 72 of https://doi.org/10.1007/BFb0065297 (Cohen-Oesterle article Dimensions des espaces de formes modulaires in Modular Functions of One Variable VI)
function lambda(r,s,p)
    assert r gt 0 and s le r;
    return 2*s gt r select 2*p^(r-s) else (2*x eq r select p^x + p^(x-1) else 2*p^x where x:= r div 2);
end function;

// Formula worked out by Kevin Buzzard in http://wwwf.imperial.ac.uk/~buzzard/maths/research/notes/dimension_of_spaces_of_eisenstein_series.pdf, with one ovious typo corrected (2*s==r, p>2 case)
function new_lambda(r,s,p)
    assert r gt 0 and s le r;
    if 2*s gt r then
        if r eq s then return 2; end if;
        if r-s eq 1 then return 2*p-4; end if;
        return 2*(p-1)^2*p^(r-s-2);
    end if;
    if 2*s eq r then
        if p eq 2 then return 0; end if;
        if s eq 1 then return p-3; end if;
        return (p-2)*(p-1)*p^(s-2);
    end if;
    if IsOdd(r) then return 0; end if;
    return r eq 2 select p-2 else (p-1)^2*p^(ExactQuotient(r,2)-2);
end function;

intrinsic QDimensionCuspForms (chi::GrpDrchElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the space S_k(N,chi) of cuspidal modular forms of weight k, level N, and character chi, where N is the modulus of chi. }
    return DimensionCuspForms(chi,k)*Degree(chi);
end intrinsic;

intrinsic QDimensionNewCuspForms (chi::GrpDrchElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the new subspace of cuspdial forms of weight k, level N, and character chi, where N is the modulus of chi. }
    return DimensionNewCuspForms(chi,k)*Degree(chi);
end intrinsic;
    
intrinsic QDimensionEisensteinForms (chi::GrpDrchElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the space E_k(N,chi) of Eisenstein series of weight k, level N, and character chi, where N is the modulus of chi. }
    require k gt 0: "The weight k must be a positive integer";
    if IsOdd(k) ne IsOdd(chi) then return 0; end if;
    N := Modulus(chi);  M := Conductor(chi);
    if N eq 1 then return k gt 2 select 1 else 0; end if;
    D := prod([lambda(Valuation(N,p),Valuation(M,p),p):p in PrimeDivisors(N)]);
    if k eq 2 and Order(chi) eq 1 then D -:= 1; end if;
    // As noted by Buzzard, to handle the weight 1 case, one simply divides by 2
    if k eq 1 then D := ExactQuotient(D,2); end if;
    return D;
end intrinsic;

intrinsic QDimensionNewEisensteinForms (chi::GrpDrchElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the new subspace of E_k(N,chi), the space of Eisenstein series of weight k, level N, and character chi, where N is the modulus of chi. }
    require k gt 0: "The weight k must be a positive integer";
    if IsOdd(k) ne IsOdd(chi) then return 0,0; end if;
    N := Modulus(chi);  M := Conductor(chi);
    if N eq 1 then return k gt 2 select 1 else 0; end if;
    D := prod([new_lambda(Valuation(N,p),Valuation(M,p),p):p in PrimeDivisors(N)]);
    if k eq 2 and Order(chi) eq 1 and IsPrime(N) then D +:= 1; end if;
    // As noted by Buzzard, to handle the weight 1 case, one simply divides by 2
    if k eq 1 then D := ExactQuotient(D,2); end if;
    return D;
end intrinsic;

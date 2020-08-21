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

intrinsic  EmbedCharacterField (chi::GrpDrchElt,k::RngIntElt,a::SeqEnum[FldNumElt]:Detail:=0) -> Map
{ Computes a Hecke-compatible embeding of Q(chi) into the coefficient field Q(f) of a weight k eigenform f of character chi with specified Fourier coefficients (NB: an error may occur if not enough coefficients are provided). }
    require k gt 0: "Weight must be a positive integer";
    print "Detail = ",Detail;
    K := NumberField(Universe(a));
    if Degree(chi) eq 1 then return hom<Rationals()->K|>; end if;
    N := Modulus(chi); e := Order(chi); F:=Codomain(chi);
    R<t>:=PolynomialRing(K);
    if Detail gt 0 then printf "Computing a primitive %oth root z of unity in number field %o...", e, DefiningPolynomial(K); t:=Cputime(); end if;
    z := Roots(R!CyclotomicPolynomial(e))[1][1];  assert z^e eq 1;
    if Detail gt 0 then printf "took %o secs\n", Cputime()-t; end if;                
    T := [r:r in [1..e-1]|GCD(r,e) eq 1];
    if Detail gt 0 then printf "Determining the correct primitive %oth root..."; t:=Cputime(); end if;
    for n:= 2 to Floor(Sqrt(#a)) do
        if GCD(N,n) ne 1 then continue; end if;
        if Detail gt 0 then printf "Checking z^%o...",n; t:=Cputime(); end if;
        T := [r:r in T|a[n]^2 eq &+[d^(k-1)*rho(chi(d))*a[ExactQuotient(n,d)^2]:d in Divisors(n)] where rho:=hom<F->K|z^r>];
        assert #T gt 0;
        if #T eq 1 then if Detail gt 0 then printf "z^%o works!\n",n; t:=Cputime(); end if; break; end if;
        if Detail gt 0 then printf "nope\n",n; t:=Cputime(); end if;
    end for;
    assert #T eq 1; // This may fail if not enough coefficients were provided
    return hom<F->K|z^T[1]>;
end intrinsic;

intrinsic EmbeddedCharacterValuesOnUnitGenerators (chi::GrpDrchElt,k::RngIntElt,a::SeqEnum[FldNumElt]:Detail:=0) -> SeqEnum[FldNumElt]
{ Given a list of Fourier coefficients for a weight k eigenform f of level N and character chi returns a list of values of chi on standard unit generators for (Z/NZ)* as elements of the coefficient field Q(f). }
    rho := EmbedCharacterField (chi,k,a:Detail:=Detail);
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

intrinsic TwistLevelBound (N::RngIntElt, chi::GrpDrchElt, psi::GrpDrchElt) -> RngIntElt
{ Upper bound (by divisibility) on the level of the newspace known to contain twist of form of level N weight k character chi by character psi. }
    require N ge 1: "Level N must be positive integers";
    return LCM([N,Conductor(psi)*Conductor(psi*chi)]);
end intrinsic;

// Uses Lemma 1.4 in  Booker, Min, Strombergsson https://arxiv.org/pdf/1803.06016.pdf, Lemma 11.2.1 in CMF paper
// No longer used for inner twists -- per Lemma 12.2.8 it suffices to check to the max of the Sturm bound and the largest Hecke cutter prime
intrinsic TwistSturmBound (N::RngIntElt, k::RngIntElt, chi::GrpDrchElt, psi::GrpDrchElt) -> RngIntElt
{ Sturm bound for space known to contain twist of form of level N weight k character chi by character psi. }
    require N ge 1 and k ge 1: "Level N and weight k must be positive integers";
//    return SturmBound(LCM([N,Conductor(phi)^2,Conductor(phi)*Conductor(chi)]),k); // weaker bound from Shimura 3.6.4
    return SturmBound(TwistLevelBound(N,chi,psi),k);
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
        printf "Computing a_p for p <= %o to check if dimension %o eigenform of level %o, weight %o, chi-conductor %o admits self-twists by %o...\n", B, Dimension(S)*Degree(chi), N, k, Conductor(chi), D;
        s := Cputime();
    end if;
    F := Eigenform(S,P[#P]+1);
    if B gt 1000 then printf "Took %.3o seconds to compute %o eigenform coefficients\n", Cputime()-s, B; end if;
    for p in P do if psi(p) eq -1 and Coefficient(F,p) ne 0 then return [Integers()|],true; end if; end for;
    return [Sign(psi)*Conductor(psi)];
end intrinsic;

// The function below relies on Lemma 11.2.1 in the CMF paper
intrinsic TwistingCharacters (chi::GrpDrchElt,chipsi2::GrpDrchElt:Conjugate:=false) -> List
{ Given characters chi of modulus N, and chipsi2 of modulus M returns a list of primitive Dirichlet characters psi for which chi*psi^2 = chipsi2,
  cond(psi)cond(chi*psi)|LCM(M,N), and M|LCM(N,cond(psi)cond(chi*psi).  If Conjugate is true, only requires chi*psi^2 to be conjugate to chipsi2.
  If f is a newform of chi and g is a twist of f by psi of character chipsi2 then psi will be in the list of reteruned characters. }
    N := Modulus(chi); M := Modulus(chipsi2); L := LCM(M,N);
    LL := IsEven(L) select LCM(L,8) else L;                  // make sure we get all possible square-roots
    n := 2*LCM(Order(chi),Order(chipsi2));
    G := DirichletGroup(LL,CyclotomicField(n));              // We will compute square-roots in G (we want to avoid using FullDirichletGroup, LL could be huge!)
    if Conjugate then
        chis :={@ G!x2/G!chi : x2 in Conjugates(chipsi2) @};  // take conjugates of chipsi2 in its ambient group, not G
        X := &join[{@ G| psi:psi in SquareRoots(chi) @}:chi in chis];
    else
        X := SquareRoots(G!chipsi2/G!chi);
    end if;
    // Apply Lemma 11.2.1 (both parts (a) and (b) are relevant)
    X := [psi : psi in X | IsDivisibleBy(LCM(N,n),M) and IsDivisibleBy(L,n) where n:=LCM(N,Conductor(psi)*Conductor(chi*psi))];
    return [* MinimalBaseRingCharacter(AssociatedPrimitiveCharacter(psi)):psi in X *];
end intrinsic;

// This function is effectively superseded by IsTwist below (just call IsTwist with g=f and AllTwists:=true)
intrinsic InnerTwists (a::SeqEnum, chi::GrpDrchElt, k::RngIntElt) -> List, RngIntElt
{ Given a list of cofficients of a newform f of character chi and weight k returns a list Dirichlet characters psi for which f*psi is conjugate to f, provided #a exceeds the Sturm bound and the largest Hecke cutter prime, result is rigorous.  Note: assumes Parent(a) = Q(f). }
    N := Modulus(chi);
    K := Universe(a);
    if Degree(K) eq 1 then return [**]; end if;
    if Order(chi) eq 1 and IsSquarefree(N) then return [**]; end if;  // we can apply Ribet Thm. 3.9 and Cor 3.10 if chi is trivial
    // Ribet Prop. 3.2 holds in general: if f has an inner twist by phi then phi must take values in Q(chi) \subseteq Q(f)
    // In fact, more is true: if chi takes nonzero values in <zeta_m> then phi takes values in <+/-zeta_m>
    // We use cond(psi)cond(chi*psi) | N, per Lemma 1.4 of Booker, Min, Strombergsson https://arxiv.org/pdf/1803.06016.pdf
    // which is also Theorem 12.2.5 in CMF paper
    X := &cat [[* psi : psi in TwistingCharacters(chi,gchi) | IsDivisibleBy(LCM(2,Order(chi)),Order(psi)) and Conductor(psi) gt 1 *] : gchi in Conjugates(chi)];
    if #X eq 0 then return [**]; end if;
    rho := EmbedCharacterField(chi,k,a);
    n := 0;
    P := [p: p in PrimesInInterval(1,#a) | GCD(N,p) eq 1 and a[p] ne 0];
    for p in P do
        f := MinimalPolynomial(a[p]);
        X := [* psi : psi in X | MinimalPolynomial(rho(psi(p))*a[p]) eq f *];
        if #X eq 0 then return [**]; end if;
        n +:= 1;
        if n eq 10 then break; end if;  // arbitrary cutoff, does not effect correctness only performance
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


// IsTwist checks whether a conjugate of g is a twist of f (i.e if [g] is a twist of [f])
// Returns a (possibly empty) list of labels of orbits of twisting characters and a correspoding list of multiplicities
intrinsic IsTwist(g::SeqEnum, gchi::GrpDrchElt, f::SeqEnum, fchi::GrpDrchElt:AllTwists:=false,Verbose:=0) -> SeqEnum, SeqEnum
{ Given lists of coefficients of newforms g and f of characters gchi and fchi, determine whether some conjugate of g may be a twist of f, and if so the orbit label of a primitive twisting character.
  If AllTwists is true then a complete list of orbit labels of twisting characters is returned, along with a corresponding list of multiplicities.
  The correctness of this result depends on the length of the given lists of coefficients, only given ap with p prime to the conductor of the twisting character are checked. }
    require #g gt 0 and #f gt 0: "g and f should be lists of at least two coefficients";

    // TODO use a Magma verbose flag
    if Type(Verbose) eq BoolElt then Verbose := Verbose select 1 else 0; end if;
    if Verbose gt 0 then start:=Cputime(); end if;
    if Verbose gt 0 then printf "Computing twisting characters...\n"; t:=Cputime(); end if;
    T := TwistingCharacters(fchi,gchi:Conjugate);  if #T eq 0 then return [Parent("")|],[Integers()|]; end if;

    // Reduce to set of character orbit reps sorted by conductor and order
    S := Sort([<Conductor(T[i]),Order(T[i]),Sprintf("%o",Sort(ConjugateAngles(CharacterAngles(T[i])))),i>: i in [1..#T]]);
    Psis := [* T[S[i][4]] : i in [1..#S] | i eq 1 or S[i][1] ne S[i-1][1] or S[i][3] ne S[i-1][3] *];
    if Verbose gt 0 then printf "Found %o twisting characters in %o character orbits (%.3os)\n", #T, #Psis, Cputime()-t; end if;

    Kf := NumberField(Universe(f)); Kg := NumberField(Universe(g)); Ag := Automorphisms(Kg);
    if Verbose gt 1 then print "Coefficients of Kf", Coefficients(DefiningPolynomial(Kf)); end if;
    if Verbose gt 1 then print "Coefficients of Kg", Coefficients(DefiningPolynomial(Kg)); end if;

    // Create ambient field K into which we can embed both Kf and Kf (which need not be normal!)
    if Verbose gt 0 then printf "Creating ambient field containing coefficient fields of degrees %o and %o (%.3os)\n", Degree(Kf), Degree(Kg), Cputime()-t; t:=Cputime(); end if;
    K,piKf,piKg := AmbientField(Kf,Kg);
    if Verbose gt 1 then print "Coefficients of K", Coefficients(DefiningPolynomial(K)); end if;
    if Verbose gt 0 then printf "Ambient field K has degree %o (%.3os)\n", Degree(K), Cputime()-t; end if;

    // Compute a torsion generator for K (note that K may be horrible so we want to use Kf and Kg to do this if K is not equal to Kf or Kg)
    if Verbose gt 0 then printf "Computing torsion generator for ambient of degree %o\n", K; t:=Cputime(); end if;
    if DefiningPolynomial(K) eq DefiningPolynomial(Kf) or DefiningPolynomial(K) eq DefiningPolynomial(Kg) then
        zK,nK := TorsionGenerator(K);
    else
        zKf,nKf := TorsionGenerator(Kf);  zKg,nKg := TorsionGenerator(Kg);
        m := &*[Integers()|p^Valuation(nKf,p) : p in PrimeDivisors(nKf) | Valuation(nKf,p) gt Valuation(nKg,p)];
        zK := piKf(zKf^ExactQuotient(nKf,m))*piKg(zKg);  nK := m*ExactQuotient(nKg,GCD(nKg,m));
    end if;
    if Verbose gt 0 then printf "Torsion generator has order %o (%.3os)\n", nK, Cputime()-t; t:=Cputime(); end if;

    // Determine primes to check (if f[p] and g[p] are both zero every value of psi(p) works so there is nothing to check)
    P := [p:p in PrimesInInterval(1,Min(#f,#g))|f[p] ne 0 or g[p] ne 0];

    lastKpsi := RationalsAsNumberField(); L,piK,piKpsi := AmbientField(K,lastKpsi); // bogus cached values we will never use but needed to shut up Magma

    twists := []; counts := [];
    for psi in Psis do
        if Verbose gt 0 then tpsi := Cputime(); end if;
        c := Conductor(psi); n := Order(psi);
        Kpsi := NumberField(Codomain(psi));  Apsi := Automorphisms(Kpsi);
        if IsDivisibleBy(nK,n) then // if K already contains an nth root of unity we don't need to extend it
            L := K; piK := hom<K->L|L.1>;
            piKpsi := hom<Kpsi->L|piK(zK^ExactQuotient(nK,n))>;
        else
            if DefiningPolynomial(Kpsi) eq DefiningPolynomial(lastKpsi) then  // Reuse the last ambient if Kpsi has not changed
                piKpsi := hom<Kpsi->L|piKpsi(lastKpsi.1)>;
            else
                if Verbose gt 0 then printf "Extending ambient coefficient field of degree %o to include character field of degree %o for character orbit %o\n", Degree(K), Degree(Kpsi), CharacterOrbitLabel(psi); t:=Cputime(); end if;
                if Verbose gt 1 then print "Coeffs of K", Coefficients(DefiningPolynomial(K)); print "Coeffs of Kpsi", Coefficients(DefiningPolynomial(Kpsi)); end if;
                L,piK,piKpsi := AmbientField(K,Kpsi); lastKpsi := Kpsi; // this can be very expensive
                if Verbose gt 0 then printf "Ambient field has degree %o (%.3os)\n", Degree(L), Cputime()-t; end if;
            end if;
        end if;
        fL := [piK(piKf(f[p])):p in P];
        i := 1; while i le #P and GCD(c,P[i]) ne 1 do i+:=1; end while; assert i le #P; p := P[i]; // we better have at least one prime to check
        if Verbose gt 0 then printf "Computing initial list of pairs of automorphisms valid for first prime p=%o ...\n", p; t := Cputime(); end if;
        S := [<ag,apsi> : ag in Ag, apsi in Apsi | piK(piKg(ag(g[p]))) eq piKpsi(apsi(psi(p)))*fL[i]];
        if Verbose gt 0 then printf "Found %o pairs of automorphism that work at p=%o (%.3os)\n", #S, p, Cputime()-t; t:=Cputime(); end if;
        if #S eq 0 then continue; end if;
        for j:=i+1 to #P do
            p := P[j]; if GCD(c,p) ne 1 then continue; end if;
            S := [r:r in S | piK(piKg(r[1](g[p]))) eq piKpsi(r[2](psi(p)))*fL[j]];
            if #S eq 0 then break; end if;
            if Verbose gt 2 then printf "%o pairs of automorphism work up to p=%o (%.3os)\n", #S, p, Cputime()-t; t:= Cputime(); end if;
        end for;
        assert #{r[2]:r in S} eq #S;    // at most one conjugate of g should work for each conjugate of psi, but this could fail if we don't have enough ap
        if Verbose gt 0 then printf "Character orbit %o of order %o appears to give %o twists (%.3os)\n", CharacterOrbitLabel(psi), Order(psi), #S, Cputime()-tpsi; end if;
        if #S gt 0 then Append(~twists,CharacterOrbitLabel(psi)); Append(~counts,#S); if not AllTwists then return twists,counts; end if; end if;
    end for;
    if Verbose gt 0 then printf "Total time %.3os\n", Cputime()-start; end if;
    if #twists le 1 then return twists, counts; end if;
    S := Sort([<twists[i],counts[i]>:i in [1..#twists]],func<a,b|CompareCharacterOrbitLabels(a[1],b[1])>);
    return [r[1]:r in S], [r[2]:r in S];
end intrinsic;

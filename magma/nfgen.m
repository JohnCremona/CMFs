Attach("zbasis.m");

function sum(x) return #x eq 0 select 0 else &+x; end function;
function prod(x) return #x eq 0 select 1 else &*x; end function;

// Code to enumerate cyclic cubic fields by conductor, based on Toru Komatsu's paper "Cyclic cubic field with explicit Artin Symbols"
// https://doi-org.libproxy.mit.edu/10.3836/tjm/1184963654

function c(p)
    if p eq 3 then return 0; end if;
    assert IsPrime(p) and p mod 3 eq 1;
    R<x,y,z>:=PolynomialRing(Rationals(),3);
    P2:=ProjectiveSpace(R);
    S := RationalPoints(Curve(P2,x^2+x*y+y^2-p*z^2):Bound:=Ceiling(Sqrt(p)));
    S := [P:P in S|P[3] eq 1 and P[2] gt 0 and Integers()!P[2] mod 3 eq 0 and P[1]/P[2] ge -1/2];
    assert #S eq 1;
    return S[1][1]/S[1][2];
end function;

function Tneg(s) return -s-1; end function;
function Tadd(s,t) return (s*t-1)/(s+t+1); end function;
function Tsum(a) assert #a gt 0; s := a[1]; for i:=2 to #a do s := Tadd(s,a[i]); end for; return s; end function;

function Tplus(f)
    S := {Rationals()|};
    if f lt 7 or not Valuation(f,3) in [0,2] then return S; end if;
    assert f gt 0;
    _,s := SquareFree(f);
    if not s in [1,3] then return S; end if;
    P := PrimeDivisors(f);
    if #[p:p in P|p mod 3 eq 2] gt 0 then return S; end if;
    C := [c(p):p in P];
    for X in Subsets(Set([1..#P])) do
        if #X eq 0 then Include(~S,Tsum(C)); continue; end if;
        if #X eq #P then Include(~S,Tneg(Tsum(C))); continue; end if;
        Include(~S,Tadd(Tneg(Tsum([C[i]:i in X])),Tsum([C[i]:i in [1..#P]|not i in X])));
    end for;
    return {s:s in S|s ge -1/2};
end function;

function Lfield(s)
    R<X>:=PolynomialRing(Rationals());
    return NumberField(Polredabs(X^3-3*s*X^2-(3*s+3)*X-1));
end function;

intrinsic CyclicCubicFieldsOfConductor (f::RngIntElt) -> SeqEnum[FldNum]
{ Returns a list of the cyclic cubic fields with the specified conductor. }
    return [Lfield(s):s in Tplus(f)];
end intrinsic;

intrinsic S4QuarticFromSextic (f::RngUPolElt) -> RngUPolElt
{ Given an S4 sextic polynomial f returns an S4 quartic with the same splitting field. }
    /*
        The following script was used to generate the hard-wired assignments below:
        
        r := PolynomialRing(Rationals(),6);
        Rr<X> := PolynomialRing(r);
        S := {r.i:i in [1..6]};
        A := SFAElementary(Rationals());
        T := {&*[x:x in a]+&*[x:x in S diff a]: a in Subsets(S,3)};
        f := &*[X-t:t in T];
        Ra<a0,a1,a2,a3,a4,a5> := PolynomialRing(Rationals(),6);
        a := [-a5,a4,-a3,a2,-a1,a0];
        for d := 0 to 9 do
            s,c := Support(RestrictParts(A!Coefficient(f,d),6:Exact:=false));
            printf "b%o := %o;\n", d, &+[c[i]*&*[a[j]:j in s[i]]:i in [1..#s]];
        end for;
    */
    for n:=1 to 7 do
        a0 := Coefficient(f,0); a1 := Coefficient(f,1); a2 := Coefficient(f,2); a3 := Coefficient(f,3); a4 := Coefficient(f,4); a5 := Coefficient(f,5);
        b0 := 8*a0^4*a3*a5^3 - 4*a0^4*a4*a5^4 + a0^4*a5^6 - 4*a0^3*a1*a2*a5^3 - 12*a0^3*a1*a3^2*a5 + 8*a0^3*a1*a3*a4*a5^2 - 2*a0^3*a1*a3*a5^4 + a0^3*a2^2*a5^4 - 2*a0^3*a2*a3^2*a5^2 + a0^3*a3^4 + 8*a0^2*a1^3*a3 - 4*a0^2*a1^3*a4*a5 + 2*a0^2*a1^3*a5^3 + 8*a0^2*a1^2*a2*a3*a5 - 2*a0^2*a1^2*a2*a4*a5^2 - 2*a0^2*a1^2*a3^2*a4 + a0^2*a1^2*a3^2*a5^2 - 4*a0*a1^4*a2 - 2*a0*a1^4*a3*a5 + a0*a1^4*a4^2 + a1^6;
        b1 := 8*a0^4*a5^3 + 24*a0^3*a1*a3*a5 - 16*a0^3*a1*a4*a5^2 + 2*a0^3*a1*a5^4 - 8*a0^3*a2*a3*a5^2 + a0^3*a2*a5^5 - 8*a0^3*a3^3 + 8*a0^3*a3^2*a4*a5 - 3*a0^3*a3^2*a5^3 + 8*a0^2*a1^3 - 16*a0^2*a1^2*a2*a5 - 8*a0^2*a1^2*a3*a4 + 6*a0^2*a1^2*a3*a5^2 + 8*a0^2*a1^2*a4^2*a5 - 3*a0^2*a1^2*a4*a5^3 + 8*a0^2*a1*a2^2*a5^2 + 8*a0^2*a1*a2*a3^2 - 8*a0^2*a1*a2*a3*a4*a5 + a0^2*a1*a2*a3*a5^3 + a0^2*a1*a3^3*a5 + 2*a0*a1^4*a5 - 3*a0*a1^3*a2*a5^2 - 3*a0*a1^3*a3^2 + a0*a1^3*a3*a4*a5 + a1^5*a4;
        b2 := 36*a0^3*a1*a5 - 6*a0^3*a2*a5^2 + 18*a0^3*a3^2 - 24*a0^3*a3*a4*a5 - 4*a0^3*a3*a5^3 + 8*a0^3*a4^2*a5^2 - a0^3*a4*a5^4 - 6*a0^2*a1^2*a4 - 7*a0^2*a1^2*a5^2 - 24*a0^2*a1*a2*a3 - 4*a0^2*a1*a2*a4*a5 + 10*a0^2*a1*a2*a5^3 + 8*a0^2*a1*a3^2*a5 + 8*a0^2*a1*a3*a4^2 - 8*a0^2*a1*a3*a4*a5^2 + a0^2*a1*a3*a5^4 + 8*a0^2*a2^2*a3*a5 - 2*a0^2*a2^2*a4*a5^2 - 2*a0^2*a2*a3^2*a4 + a0^2*a2*a3^2*a5^2 - 4*a0*a1^3*a3 + 10*a0*a1^3*a4*a5 - 4*a0*a1^3*a5^3 + 8*a0*a1^2*a2^2 - 8*a0*a1^2*a2*a3*a5 - 2*a0*a1^2*a2*a4^2 + a0*a1^2*a2*a4*a5^2 + a0*a1^2*a3^2*a4 - a1^4*a2 + a1^4*a3*a5;
        b3 := -9*a0^3*a5^3 - 39*a0^2*a1*a3*a5 + 14*a0^2*a1*a4*a5^2 - a0^2*a1*a5^4 + 11*a0^2*a2*a3*a5^2 - 2*a0^2*a2*a4*a5^3 + 3*a0^2*a3^3 - 3*a0^2*a3^2*a4*a5 + a0^2*a3^2*a5^3 - 9*a0*a1^3 + 14*a0*a1^2*a2*a5 + 11*a0*a1^2*a3*a4 - 6*a0*a1^2*a3*a5^2 - 3*a0*a1^2*a4^2*a5 + a0*a1^2*a4*a5^3 - 3*a0*a1*a2^2*a5^2 - 3*a0*a1*a2*a3^2 + a0*a1*a2*a3*a4*a5 - a1^4*a5 - 2*a1^3*a2*a4 + a1^3*a2*a5^2 + a1^3*a3^2;
        b4 := -27*a0^3 - 30*a0^2*a1*a5 + 18*a0^2*a2*a4 - 2*a0^2*a2*a5^2 - 15*a0^2*a3^2 + 16*a0^2*a3*a4*a5 + a0^2*a3*a5^3 - 4*a0^2*a4^3 - a0^2*a4^2*a5^2 - 2*a0*a1^2*a4 + 6*a0*a1^2*a5^2 + 16*a0*a1*a2*a3 - 3*a0*a1*a2*a5^3 - a0*a1*a3^2*a5 - 2*a0*a1*a3*a4^2 + a0*a1*a3*a4*a5^2 - 4*a0*a2^3 - 2*a0*a2^2*a3*a5 + a0*a2^2*a4^2 + a1^3*a3 - 3*a1^3*a4*a5 + a1^3*a5^3 - a1^2*a2^2 + a1^2*a2*a3*a5;
        b5 := 9*a0^2*a3 + 3*a0^2*a4*a5 + 2*a0^2*a5^3 + 3*a0*a1*a2 + 16*a0*a1*a3*a5 - 4*a0*a1*a4^2 - 2*a0*a1*a4*a5^2 - 4*a0*a2^2*a5 - a0*a2*a3*a4 - 2*a0*a2*a3*a5^2 + a0*a2*a4^2*a5 + 2*a1^3 - 2*a1^2*a2*a5 - 2*a1^2*a3*a4 + a1^2*a3*a5^2 + a1*a2^2*a4;
        b6 := 27*a0^2 + 9*a0*a1*a5 - 9*a0*a2*a4 + a0*a2*a5^2 + 3*a0*a3^2 - 3*a0*a3*a4*a5 + a0*a4^3 + a1^2*a4 - a1^2*a5^2 - 3*a1*a2*a3 + a1*a2*a4*a5 + a2^3;
        b7 := -6*a0*a3 - a0*a4*a5 - a1*a2 - 2*a1*a3*a5 + a1*a4^2 + a2^2*a5;
        b8 := -9*a0 - a1*a5 + a2*a4;
        b9 := a3;
        g := Parent(f)![b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,1];
        A := Factorization(g);
        A := [a[1]:a in A|Degree(a[1]) eq 4];
        if #A eq 1 and IsEasySnAn(A[1]) eq 1 then return Polredabs(A[1]); end if;
        // Shift input poly to break symmetry if needed, this won't work in small characteristic.
        f:=Evaluate(f,Parent(f).1+n);
    end for;
    if Identify(GaloisGroup(f)) eq <24,12> then
        error "Unable to find S4-quartic sibling of input sextic after 7 shifts, WTF?!";
    else
        error Sprintf("Input to S4QuarticFromSextic is not an S4 sextic: %o",f);
    end if;
end intrinsic;

// Use the Algorithm of Cohen, Diaz-Y-Diaz, and Olivier to construct S4 field from S3 field with constrained ramification
// See pp. 945-946 of http://www.ams.org/journals/mcom/2003-72-242/S0025-5718-02-01452-7/S0025-5718-02-01452-7.pdf
// We don't bother trying to optimize generators (revisit if necessary)
intrinsic S4Fields (f::SeqEnum,P::SeqEnum[RngIntElt]) -> SeqEnum[RngIntElt]
{ Given a cubic polynomial f with S3 splitting field returns a list of quartic polynomials with S4 splitting fields contain the splitting field of f unramified outside the list of primes P and the ramification of f.}
    require #f eq 4: "First parameter must specify an irreducible cubic";
    require #P eq 0 or &and[IsPrime(p):p in P]: "Second parameter must be a list of primes";
    K := NumberField(PolynomialRing(Rationals())!f);
    OK := RingOfIntegers(K);
    U,piU := UnitGroup(OK);
    U := [piU(u) : u in Generators(U) | Order(u) eq 0];
    G,piG := ClassGroup(OK);
    H,piH := quo<G|[2*g:g in Generators(G)]>;
    e := Invariants(G);
    ei := [IsEven(i) select 1/2 else Rationals()!InverseMod(2,i) : i in e];
    halve := func<g|G![Integers()!(ei[j]*gg[j]) mod e[j] : j in [1..#e]] where gg := Eltseq(g)>;
    assert &and[Order(G.i) eq e[i] : i in [1..#e]];
    X := [piG(G.i) : i in [1..#e] | IsEven(e[i])];
    E := [e[i] : i in [1..#e] | IsEven(e[i])];
    two := ideal<OK|2>;
    V := [MakeCoprime(I,two)*I : I in X];
    V := [v where _,v:=IsPrincipal(V[i]^E[i]) : i in [1..#V]] cat U;
    V := {IsSquare(-Norm(v)) select -v else v : v in V};
    A := [];
    Q := 2 in P select P else [2] cat P;
    for p in Q do
        pp := Factorization(ideal<OK|p>);
        case #pp:
        when 3: for i:=1 to 3 do Append(~A,&*[pp[j][1]:j in [1..3] | j ne i]); end for;
        when 2: pp2 := [q[1]:q in pp | Degree(q[1]) eq 2]; Append(~A, #pp2 gt 0 select pp2[1] else pp[1][1]*pp[2][1]);
        end case;
    end for;
    A := [ideal<OK|prod(s)> : s in Subsets(Set(A))];
    A := [a : a in A | Radical(a) eq a];
    A := [a : a in A | IsIdentity(piH(Inverse(piG)(a)))];  // only keep ideals whose class is square
    A := [alpha where _,alpha := IsPrincipal(a*(MakeCoprime(b,two)*b)^2) where b := piG(halve(-Inverse(piG)(a))) : a in A];
    A := [IsSquare(Norm(alpha)) select alpha else -alpha : alpha in A];
    X := &cat[[Polredabs([f[3]^2-4*f[2],-8*s,2*f[3],0,1]) where _,s := IsSquare(-f[1]) where f:=Coefficients(MinimalPolynomial(alpha*u)) where u := prod(v) : v in Subsets(V) |#v gt 0 or alpha ne 1] : alpha in A];
    Pf := Set(P cat PrimeDivisors(NFDiscriminant(f)));
    return [f : f in X | Set(PrimeDivisors(NFDiscriminant(f))) subset Pf];
end intrinsic;

intrinsic S4Fields (f::RngUPolElt,P::SeqEnum[RngIntElt]) -> RngUPolElt
{ Given a cubic polynomial f with S3 splitting field returns a list of quartic polynomials with S4 splitting fields contain the splitting field of f unramified outside the list of primes P and the ramification of f.}
    R<x>:=PolynomialRing(Rationals());
    return [R!g : g in S4Fields(Eltseq(f),P)];
end intrinsic;

intrinsic S4FieldsOld (f::RngUPolElt,M::RngIntElt) -> SeqEnum[RngUPolElt]
{ Given a cubic polynomial f with S3 splitting field returns a list of quartic polynomials with S4 splitting fields contain the splitting field of f unramified outside M and the ramification of f.}
    require Degree(f) eq 3 and IsEasySnAn(f) eq 1: "Input polynomial must be an S3 cubic";
    K := NumberField(f);  P := [i:i in [1..#RealPlaces(K)]];
    OK := RingOfIntegers(K);
    I := Sort([c:c in Divisors(ideal<OK|M>)|IsDivisibleBy(M,Norm(c))],func<a,b|Norm(a)-Norm(b)>);
    L := {}; X := {};
printf "%o conductors\n", #I;
    for c in I do
        G,mG := RayClassGroup(c,P);
printf "Ray class for conductor of norm %o has %o quotients of order 2\n", Norm(c), #Subgroups(G:Quot:=[2]);
        for C in Subgroups(G:Quot:=[2]) do
            H,mH := quo<G|C`subgroup>;
            mGH := mH^-1*mG;
            f := DefiningPolynomial(AbsoluteField(NumberField(AbelianExtension(mGH))));
            if f in X then continue; end if;
            if IdentifyGroup(GaloisGroup(f)) eq <24,12> then Include(~L,S4QuarticFromSextic(f)); end if;
        end for;
    end for;
    return L;
end intrinsic;
        
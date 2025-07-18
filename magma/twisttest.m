/*
for N in [64,27,25,49,121,13,17,19,23,29,31,37] do
    b,p,e := IsPrimePower(N); assert b;
    for a:=1 to 2*e do
        for c in CharacterOrbitReps(p^a:OrderBound:=EulerPhi(p^e)) do
            if QDimensionNewCuspForms(c,2) gt 0 then
                printf "magma -b chi:=%o k:=2 mfdump.m\n", CharacterOrbitLabel(c);
            end if;
        end for;
    end for;
end for;

for N in [13,17,19,23,29,31,37] do
    b,p,e := IsPrimePower(N); assert b;
    for a:=1 to 2*e do
        for c in CharacterOrbitReps(p^a:OrderBound:=EulerPhi(p^e)) do
            if QDimensionNewCuspForms(c,2) gt 0 and not IsMinimal(c) then
                printf "magma -b chi:=%o mftwistdump.m\n", CharacterOrbitLabel(c);
            end if;
        end for;
    end for;
end for;
*/

function ppchars(level)
    b,p,e := IsPrimePower(level);
    assert b;
    return &cat[[s:s in ConreyCharacterOrbitReps(p^a)|Parity(s) eq 1 and Conductor(s) le p^e and QDimensionNewCuspForms(s,2) gt 0]:a in [1..2*e]];
end function;

function mintwists(tchi)
    if StringToCode(Split(tchi,".")[2]) gt StringToCode("9") then tchi := ConreyConjugates(tchi)[1]; end if;
    N := Modulus(tchi);
    b,p,e:= IsPrimePower(N);  assert b;
    M := &cat[[s:s in ConreyCharacterOrbitReps(p^a)|IsMinimal(s)]:a in [1..e]];
    P := &cat[[Sprintf("%o.%o",p^a,n):n in [1..p^a-1]|n mod p ne 0]:a in [1..4]];
    P := [psi:psi in P|IsPrimitive(psi)];
    P2 := [ConreyCharacterProduct(psi,psi):psi in P];
    tcond := Conductor(tchi);
    return Sort([[chi,P[i],Twist(chi,P[i])]:chi in M, i in [1..#P]|ConductorProduct(chi,P2[i]) eq tcond and Twist(chi,P[i]) eq tchi]);
end function;

function loadcoeffs(chi)
    chi := DirichletCharacter(chi);
    c := Split(CharacterOrbitLabel(chi),".");
    S := getrecs(Sprintf("cmf_dump_%o.2.%o.txt",c[1],c[2]));
    chilabel := ConreyLabel(chi);
    assert &and[s[2] eq chilabel:s in S];
    A := [**];
    for s in S do
        dim := atoi(s[4]);
        F := Codomain(chi);
        if Degree(F) eq 1 or Degree(F) eq dim then
            K := NumberField(atoii(s[8]));
            Append(~A,<s[1],s[2],dim,[K|c:c in eval(s[9])]>);
        else
            K := NumberField(PolynomialRing(F)![F|c:c in atoiii(s[8])]);
            Append(~A,<s[1],s[2],dim,[K|[F|c:c in a]:a in eval(s[9])]>);
        end if;
    end for;
    return A;
end function;

function loadhashes(chi)
    c := Split(CharacterOrbitLabel(chi),".");
    S := getrecs(Sprintf("cmf_dump_%o.2.%o.txt",c[1],c[2]));
    assert &and[s[2] eq chi:s in S];
    return [[s[1],s[4],s[5]]:s in S];
end function;

function twist(chi,a,psi:ComputeAnalyticRank:=false)
    K := Parent(a[1]);
    tchi := Twist(chi,psi);
    zchi := CyclotomicConreyCharacter(chi);  zpsi := CyclotomicConreyCharacter(psi);  ztchi := CyclotomicConreyCharacter(tchi);
    assert BaseField(K) eq Codomain(zchi) or (BaseField(K) eq Rationals() and DefiningPolynomial(K) eq DefiningPolynomial(Codomain(zchi)));
    P := PrimesInInterval(1,8192);
    assert #a ge #P;
    // the conditions below do not  hold in general, but they do in the specific cases we need to handle
    if Degree(zpsi) le Degree(zchi) then
        assert Degree(zpsi) eq 1 or IsSubfield(Codomain(zpsi),Codomain(zchi));
        dim := AbsoluteDegree(K);
        Tps := [[Integers()|Trace(Trace(a[i])*zpsi(P[i])):i in [1..#P]]];
    else
        assert IsSubfield(Codomain(zchi),Codomain(zpsi));
        if not IsIrreducible(ChangeRing(DefiningPolynomial(K),Codomain(zpsi))) then
            L := AbsoluteField(K);
            tmaps := TraceProductMaps(L,Codomain(zpsi));
            dim := tmaps[1](1,1);
            Tps := [[Integers()|tmap(L!a[i],zpsi(P[i])):i in [1..#P]]:tmap in tmaps];
        else
            dim := Degree(K)*Degree(zpsi);
            L := RelativeField(Codomain(zchi),Codomain(zpsi));
            Tps := [[Integers()|Trace(Trace(a[i])*Trace(L!zpsi(P[i]))):i in [1..#P]]];
        end if;
    end if;
    Tps := Sort([t:t in Set(Tps)]);
    hs := [TraceHash(Tp):Tp in Tps];
    if not ComputeAnalyticRank then return tchi,dim,hs,Tps; end if;
    e := AbsoluteDegree(K) eq 1 select [] else (Degree(BaseField(Universe(a))) eq 1 select [1] else [1,1]);
    prec := 60;
    while true do
        CC := ComplexField(prec);
        cpsi := ComplexConreyCharacter(psi,CC);
        ctchi := ComplexConreyCharacter(tchi,CC);
        cc := e eq [] select func<x|CC!x> else func<z|Conjugate(z,e:Prec:=prec)>;
        time ta := [cpsi(P[i])*cc(a[i]):i in [1..#P]];
        xi := [ctchi(P[i]):i in [1..#P]];
        time r := CCAnalyticRank(Modulus(ztchi),xi,2,ta);
        if r ge 0 then break; end if;
        prec *:= 2;
        print "Increasing precision to",prec;
        assert prec le 100000;
    end while;
    return tchi,dim,hs,Tps,r;
end function;

procedure dumptwists(tchi)
    start := Cputime();
    H := {}; S := [];
    for r in mintwists(tchi) do
        if QDimensionNewCuspForms(r[1],2) eq 0 then continue; end if;
        printf "Twisting %o by %o\n", r[1],r[2];
        A := loadcoeffs(r[1]);
        for a in A do
            printf "Twisting form %o of dimension %o and character %o by %o of degree %o...", a[1], a[3], a[2], r[2], Degree(r[2]);
            assert a[2] eq r[1];
            t := Cputime();
            ttchi,dim,hs,Tps,rank := twist(r[1],a[4],r[2]:ComputeAnalyticRank);
            assert CharacterOrbitLabel(ttchi) eq tchi;
            printf "...took %.3o secs\n", Cputime()-t;
            for i:= 1 to #hs do
                if not <hs[i],Tps[i]> in H then
                    Include(~H,<hs[i],Tps[i]>);
                    Append(~S,<Sprintf("%.3o",Cputime()-t),dim,hs[i],Tps[i],rank>);
                end if;
            end for;
        end for;
        printf "We now have twists of dimensions %o\n", {* r[2]:r in S *};
    end for;
    c := Split(CharacterOrbitLabel(tchi),".");
    S := Sort([r:r in S],func<a,b|a[4] lt b[4] select -1 else 1>);
    S := [[Sprintf("%o.2.%o.%o",c[1],c[2],Base26Encode(i)), tchi] cat [sprint(c):c in S[i]] : i in [1..#S]];
    filename := Sprintf("cmf_tdump_%o.2.%o.txt",c[1],c[2]);
    n := putrecs(filename,S);
    printf "Wrote %o newforms to file %o, total time %.3o secs\n", #S, filename, Cputime()-start;
end procedure;

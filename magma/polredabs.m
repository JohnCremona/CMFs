function get_gp_coeffs(s)
    return [StringToInteger(x) : x in Split(s[Index(s,"[")+1..Index(s,"]")-1],",")];
end function;

// use polredabs and polrebest rather than Polredabs and Polredbest to avoid collision with CHIMP

intrinsic polredabs(f::SeqEnum:DiscFactors:=[]) -> SeqEnum
{ Computes a smallest canonical defining polynomial of the etale algebra Q[x]/(f(x)) using pari. }
    cmd := #DiscFactors eq 0 select Sprintf("{print(Vecrev(Vec(polredabs(Pol(Vecrev(%o))))))}", f) else  Sprintf("{print(Vecrev(Vec(polredabs([Pol(Vecrev(%o)),%o]))))}", f,DiscFactors);
    s := Pipe("gp -q", cmd);
    return get_gp_coeffs(s);
end intrinsic;

intrinsic polredabs(f::RngUPolElt:DiscFactors:=[]) -> RngUPolElt
{ Computes a smallest canonical defining polynomial of the etale algebra Q[x]/(f(x)) using pari. }
    return Parent(f)!polredabs(Coefficients(f):DiscFactors:=DiscFactors);
end intrinsic;

intrinsic polredbest(f::SeqEnum:DiscFactors:=[]) -> SeqEnum
{ Computes a small (non-canonical) defining polynomial of the etale algebra Q[x]/(f(x)) using pari. }
    cmd := #DiscFactors eq 0 select Sprintf("{print(Vecrev(Vec(polredbest(Pol(Vecrev(%o))))))}", f) else  Sprintf("{print(Vecrev(Vec(polredbest([Pol(Vecrev(%o)),%o]))))}", f,DiscFactors);
    s := Pipe("gp -q", cmd);
    return get_gp_coeffs(s);
end intrinsic;

intrinsic polredbest(f::RngUPolElt:DiscFactors:=[]) -> RngUPolElt
{ Computes a small (non-canonical) defining polynomial of the etale algebra Q[x]/(f(x)) using pari. }
    return Parent(f)!polredbest(Coefficients(f):DiscFactors:=DiscFactors);
end intrinsic;

intrinsic PerfectPowerBase(n::RngIntElt) -> RngIntElt
{ Returns the least positive integer m such that m^e = n for some positive integer e (m=n if n is not a perfect power). }
    assert n ge 0;
    if n lt 2 then return n; end if;
    b,m := IsPower(n);
    return b select m else n;
end intrinsic

intrinsic IsPolredabsCandidate (f::RngUPolElt) -> BoolElt
{ Returns true if the polynomial looks like Polredabs can easily handle it. }
    if Degree(f) gt 64 then return false; end if;
    n := PerfectPowerBase(Integers()!AbsoluteValue(Discriminant(f)));
    if n le 10^80 then return true; end if;
    _,s := TrialDivision(n,10^6);
    if #s eq 0 then return true; end if;
    n := PerfectPowerBase(Max(s));
    _,s := PollardRho(n);
    if #s eq 0 then return true; end if;
    n := PerfectPowerBase(Max(s));
    for i:=1 to 5 do
        d := ECM(n,10^4);
        if d gt 0 then
            n := ExactQuotient(n,d);
            n := PerfectPowerBase(n);
        end if;
    end for;
    return n le 10^80 or IsProbablePrime(n);
end intrinsic;

intrinsic IsPolredabsCandidate (f::SeqEnum) -> SeqEnum
{ Returns true if the polynomial looks like Polredabs can easily handle it. }
    return IsPolredabsCandidate(PolynomialRing(Integers())!f);
end intrinsic;

intrinsic Polredbestify (f::RngUPolElt:DiscFactors:=[]) -> RngUPolElt, BoolElt
{ Call polredbest repeatedly to get s smaller defining polynomial for the etale algebra Q[x]/(f(x)) using pari. } 
    for n:=1 to 5 do
        g := f;
        f := polredbest(g:DiscFactors:=DiscFactors);
        if f eq g then break; end if;
    end for;
    if #DiscFactors gt 0 then return polredabs(f),true; end if;
    if IsPolredabsCandidate(f) then return polredabs(f),true; else return f,false; end if;
end intrinsic;

intrinsic polredbestify (f::SeqEnum:DiscFactors:=[]) -> RngUPolElt, BoolElt
{ Call polredbest repeatedly to get s smaller defining polynomial for the etale algebra Q[x]/(f(x)) using pari. } 
    f,b := Polredbestify(PolynomialRing(Integers())!f:DiscFactors:=DiscFactors);
    return Eltseq(f),b;
end intrinsic;

intrinsic PolredbestWithRoot(f::RngUPolElt) -> RngUPolElt, SeqEnum
{ Returns small polynomial as in Polredbest together with a root, using pari. }
    cmd := Sprintf("{u = polredbest(Pol(Vecrev(%o)),1); print(Vecrev(Vec(u[1])),Vecrev(Vec(lift(u[2]))))}", Coefficients(f));
    s := Pipe("gp -q", cmd);
    c := Index(s,"]");
    spol := s[1..c];
    sroot := s[c+1..c+Index(s[c+1..#s],"]")];
    sspol := [ StringToInteger(x) : x in Split(spol, ", []\n") | x ne "" ];
    ssroot := [ StringToRational(x) : x in Split(sroot, ", []\n") | x ne "" ];
    ssroot cat:= [0 : i in [1..Degree(f)-#ssroot]];
    return Parent(f) ! sspol, ssroot;
end intrinsic;

intrinsic PolredabsWithRoot(f::RngUPolElt) -> RngUPolElt, SeqEnum
{ Returns Polredabs(f) together with a root, using pari. }
    cmd := Sprintf("{u = polredabs(Pol(Vecrev(%o)),1); print(Vecrev(Vec(u[1])),Vecrev(Vec(lift(u[2]))))}", Coefficients(f));
    s := Pipe("gp -q", cmd);
    c := Index(s,"][");
    spol := s[1..c];
    sroot := s[c+1..c+Index(s[c+1..#s],"]")];
    sspol := [ StringToInteger(x) : x in Split(spol, ", []\n") | x ne "" ];
    ssroot := [ StringToRational(x) : x in Split(sroot, ", []\n") | x ne "" ];
    ssroot cat:= [0 : i in [1..Degree(f)-#ssroot]];
    return Parent(f) ! sspol, ssroot;
end intrinsic;

intrinsic PolredbestifyWithRoot(f::RngUPolElt) -> RngUPolElt, SeqEnum, BoolElt
{ Returns small polynomial as in Polredbestify together with a root, using pari.  Will use polredabs if this seems feasible (this is indicated by the third return value) }
    if IsPolredabsCandidate (f) then g,r := PolredabsWithRoot(f);  return g,r,true; end if;
    K0 := NumberField(f);
    iota := hom<K0 -> K0 | K0.1>; // start with identity
    cnt := 0;
    Kfront := K0;
    ffront := f;
    polredabsflag := false;
    for n:=1 to 5 do
        fbest, fbestroot := PolredbestWithRoot(ffront);
        if fbest eq ffront then
            if IsPolredabsCandidate (fbest) then
                fbest, fbestroot := PolredabsWithRoot(ffront); polredabsflag := true;
            else
                break;
            end if;
        end if;
        Kbest := NumberField(fbest);
        iota := iota*hom<Kfront -> Kbest | fbestroot>;
        Kfront := Kbest;
        ffront := fbest; 
        if polredabsflag then break; end if;
    end for;
    return ffront, Eltseq(iota(K0.1)), polredabsflag;
end intrinsic;

intrinsic nfisincl(f::RngUPolElt,g::RngUPolElt) -> SeqEnum[RngUPolElt]
{ Returns a list of polynomials defining embeddings of the number field K defined by g in the number field L defined by f (each is specified by a polynomial h for which h(L.1) is a generator for the embedding of K in L). }
    require BaseRing(f) eq Rationals() or BaseRing(f) eq Integers(): "The polynomial f must have coefficients in Q.";
    require BaseRing(g) eq Rationals() or BaseRing(g) eq Integers(): "The polynomial g must have coefficients in Q.";
    x := Parent(g).1;
    f := Evaluate(f,x);
    cmd:=Sprintf("{print(nfisincl(%o,%o))}",f,g);
    s := strip(Pipe("gp -q", cmd));
    if s eq "0" then return [Parent(g)|]; end if;
    s := eval(s);
    return [Parent(g)|Evaluate(h,x):h in s];
end intrinsic;

intrinsic Polredabs(f::RngUPolElt) -> RngUPolElt
{ Computes a smallest canonical defining polynomial of the etale algebra Q[x]/(f(x)) using pari. }
    cmd := Sprintf("{print(Vecrev(Vec(polredabs(Pol(Vecrev(%o))))))}", Coefficients(f));
    s := Pipe("gp -q", cmd);
    ss := [ StringToInteger(x) : x in Split(s, ", []\n") | x ne "" ];
    return Parent(f) ! ss;
end intrinsic;

intrinsic Polredbest(f::RngUPolElt) -> RngUPolElt
{ Computes a small (non-canonical) defining polynomial of the etale algebra Q[x]/(f(x)) using pari. }
    cmd := Sprintf("{print(Vecrev(Vec(polredbest(Pol(Vecrev(%o))))))}", Coefficients(f));
    s := Pipe("gp -q", cmd);
    ss := [ StringToInteger(x) : x in Split(s, ", []\n") | x ne "" ];
    return Parent(f) ! ss;
end intrinsic;

intrinsic PerfectPowerBase(n::RngIntElt) -> RngIntElt
{ Returns the least positive integer m such that m^e = n for some positive integer e (m=n if n is not a perfect power). }
    assert n ge 0;
    if n lt 2 then return n; end if;
    b,m := IsPower(n);
    return b select m else n;
end intrinsic

intrinsic IsPolredabsCandidate (f::RngUPolElt) -> RngUPolElt
{ Returns true if the polynomial looks like Polredabs can easily handle it. }
    if Degree(f) gt 32 then return false; end if;
    n := PerfectPowerBase(Integers()!AbsoluteValue(Discriminant(f)));
    if n le 10^100 then return true; end if;
    for e := 5 to 7 do
        _,s := TrialDivision(n,10^e);
        if #s eq 0 then return true; end if;
        n := PerfectPowerBase(Max(s));
    end for;
    return n le 10^100 or IsProbablePrime(n);
end intrinsic;

intrinsic Polredbestify (f::RngUPolElt) -> RngUPolElt, BoolElt
{ Call Polredbest repeatedly to get s smaller defining polynomial for the etale algebra Q[x]/(f(x)) using pari. } 
    for n:=1 to 5 do
        g := f;
        f := Polredbest(g);
        if f eq g then break; end if;
    end for;
    if IsPolredabsCandidate(f) then return Polredabs(f),true; else return f,false; end if;
end intrinsic;

intrinsic PolredbestWithRoot(f::RngUPolElt) -> RngUPolElt, SeqEnum
{ Returns small polynomial as in Polredbest together with a root, using pari. }
    cmd := Sprintf("{u = polredbest(Pol(Vecrev(%o)),1); print(Vecrev(Vec(u[1])),Vecrev(Vec(lift(u[2]))))}", Coefficients(f));
    s := Pipe("gp -q", cmd);
    c := Index(s,"][");
    spol := s[1..c];
    sroot := s[c+1..#s-1];
    sspol := [ StringToInteger(x) : x in Split(spol, ", []\n") | x ne "" ];
    ssroot := [ StringToRational(x) : x in Split(sroot, ", []\n") | x ne "" ];
    return Parent(f) ! sspol, ssroot;
end intrinsic;

intrinsic PolredabsWithRoot(f::RngUPolElt) -> RngUPolElt, SeqEnum
{ Returns Polredabs(f) together with a root, using pari. }
    cmd := Sprintf("{u = polredabs(Pol(Vecrev(%o)),1); print(Vecrev(Vec(u[1])),Vecrev(Vec(lift(u[2]))))}", Coefficients(f));
    s := Pipe("gp -q", cmd);
    c := Index(s,"][");
    spol := s[1..c];
    sroot := s[c+1..#s-1];
    sspol := [ StringToInteger(x) : x in Split(spol, ", []\n") | x ne "" ];
    ssroot := [ StringToRational(x) : x in Split(sroot, ", []\n") | x ne "" ];
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
        fbestroot := fbestroot cat [0 : i in [1..Degree(fbest)-#fbestroot]];
        iota := iota*hom<Kfront -> Kbest | fbestroot>;
        Kfront := Kbest;
        ffront := fbest; 
        if polredabsflag then break; end if;
    end for;
    return ffront, Eltseq(iota(K0.1)), polredabsflag;
end intrinsic;

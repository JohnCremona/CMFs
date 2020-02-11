AttachSpec("mf.spec");

MIN_QEXP_DIGITS := 25;
MAX_QEXP_DIGITS := 45;

// Do not use SubstituteString here, it is horrendously slow
function bracket(s)
    t := Join(Split(Join(Split(s,"<":IncludeEmpty),"["),">":IncludeEmpty),"]");
    // Split omits the last field if it is empty even when IncludeEmpty is set (which makes no sense!), so we work around this by padding if needed
    if #t lt #s and s[#s] eq ">" then t cat:="]";  end if;  // don't check for trailing <, this shouldn't happen, and if it does assert below will fail
    assert #s eq #t;
    return t;
end function;

function curly(s) 
    // Split omits the last field if it is empty even when IncludeEmpty is set (which makes no sense!), so we work around this by padding if needed
    t := Join(Split(Join(Split(s,"[":IncludeEmpty),"{"),"]":IncludeEmpty),"}");
    if #t lt #s and s[#s] eq "]" then t cat:="}";  end if; // don't check for trailing [, this shouldn't happen, and if it does assert below will fail
    assert #s eq #t;
    return t;
end function;

function uncurly(s) 
    // Split omits the last field if it is empty even when IncludeEmpty is set (which makes no sense!), so we work around this by padding if needed
    t := Join(Split(Join(Split(s,"{":IncludeEmpty),"["),"}":IncludeEmpty),"]");
    if #t lt #s and s[#s] eq "}" then t cat:="]";  end if; // don't check for trailing [, this shouldn't happen, and if it does assert below will fail
    assert #s eq #t;
    return t;
end function;

function AnalyticConductor (N, k)
    return N*(Exp(Psi(k/2))/(2*Pi(RealField())))^2;
end function;

function CompareCCLists(a,b)
    for i:=1 to #a do
        if Real(a[i]) lt Real(b[i]) then return -1; end if;
        if Real(a[i]) gt Real(b[i]) then return 1; end if;
        if Imaginary(a[i]) lt Imaginary(b[i]) then return -1; end if;
        if Imaginary(a[i]) gt Imaginary(b[i]) then return 1; end if;
    end for;
    return 0;
end function;

// return latex string for cv^e, where c is an integer, v is a string (e.g. "q" or "\\\\beta"), and e is a positive integer
function LatexTerm(c,v,e:First:=false)
    if c eq 0 then return ""; end if;
    es := e eq 1 select "" else Sprintf("^{%o}",e);
    if c eq 1 then return (First select "" else "+") cat v cat es; end if;
    if c eq -1 then return "-" cat v cat es; end if;
    if Abs(c) gt 10 then b,p,n := IsPower(Abs(c)); else b := false; end if;
    s := Sign(c) eq 1 select (First select "" else "+") else "-";
    s cat:= b select Sprintf("%o^{%o}",p,n) cat v else IntegerToString(Abs(c)) cat v;
    return s cat es;
end function;

function LatexSubTerm(c,v,e:First:=false,SubscriptZeroIsOne:=false,Superscript:=false,OmitSubscriptOne:=false)
    if c eq 0 then return ""; end if;
    if SubscriptZeroIsOne and e eq 0 then
        if c eq 1 then return (First select "1" else "+1"); end if;
        if c eq -1 then return "-1"; end if;
        v:=""; es:="";
    else
        if e eq 1 then
            es := (OmitSubscriptOne or Superscript) select "" else "_{1}";
        else
            es := Superscript select Sprintf("^{%o}",e) else Sprintf("_{%o}",e);
        end if;
    end if;
    if c eq 1 then return (First select "" else "+") cat v cat es; end if;
    if c eq -1 then return "-" cat v cat es; end if;
    if Abs(c) gt 10 then b,p,n := IsPower(Abs(c)); else b := false; end if;
    s := Sign(c) eq 1 select (First select "" else "+") else "-";
    s cat:= b select Sprintf("%o^{%o}",p,n) cat v else IntegerToString(Abs(c)) cat v;
    return s cat es;
end function;

function qexp_display_len (s)
    alphabet := "abcdefghijklmnopqrstuvwxyz";
    n := 0;
    i := 1;  e := #s;
    while i le e do
        // don't count spaces or parens, count subscripts, and superscripts as half a character (rounded down)
        if s[i] in "( )" then i+:=1; continue; end if;
        if s[i] in "^_" then
            i +:= 1;
            assert i lt e and s[i] eq "{";
            j := i;
            while i le e and s[i] ne "}" do i +:= 1; end while;
            assert i le e and s[i] eq "}";
            n +:= (i-j-1) div 2;
            continue;
        end if;
        // count latex symbols like \beta and \zeta and \cdots as one character
        if s[i] eq "\\" then
            assert i+1 lt e and s[i+1] eq "\\" and s[i+2] in alphabet;
            i +:=3;
            while i le e and s[i] in alphabet do i +:= 1; end while;
            n +:= 1;
            continue;
        end if;
        // count signs as two characters
        if s[i] in "+-" then n+:=1; end if;
        // every other digit/letter gets counted as one character
        n +:= 1;  i+:=1;
    end while;
    return n;
end function;
        
function qExpansionStringOverNF(a,minlen,maxlen,root_of_unity,power_basis)
    d := #a[1];
    zero := [0: i in [1..d]];
    one := [1] cat [0:i in [2..d]];
    assert d gt 1 and a[1] eq one;
    v := root_of_unity eq 0 select "\\\\beta " else (root_of_unity eq 4 select "i" else Sprintf("\\\\zeta_{%o}",root_of_unity));
    ss := root_of_unity gt 0 or power_basis ne 0;
    oso := d le 2;
    s := "q";  t := s;
    n := 2;
    while qexp_display_len(s) lt minlen and n le #a do
        t := s;
        if a[n] ne zero then
            if &and[a[n][i] eq 0 : i in [2..#a[n]]] then
                s cat:= LatexTerm(a[n][1],"q",n);
             else
                if #[c:c in a[n]|c ne 0] eq 1 then
                    i:=[j:j in [1..#a[n]]|a[n][j] ne 0][1];
                    s cat:= LatexSubTerm(a[n][i],v,i-1:SubscriptZeroIsOne,Superscript:=ss,OmitSubscriptOne:=oso);
                else
                    s cat:= "+(";
                    i := 1;
                    while i le #a[n] do
                        if a[n][i] ne 0 then
                            s cat:= LatexSubTerm(a[n][i],v,i-1:First:=(s[#s] eq "("),SubscriptZeroIsOne,Superscript:=ss,OmitSubscriptOne:=oso);
                            if qexp_display_len(s) gt minlen then i +:= 1; break; end if;
                        end if;
                        i +:=1;
                    end while;
                    s cat:= i le #a[n] select "+\\\\cdots)" else ")";
                end if;
                s cat:= Sprintf("q^{%o}",n);
            end if;
        end if;
        n +:= 1;
    end while;
    return (qexp_display_len(s) le maxlen select s else t) cat "+\\\\cdots";
end function;

function qExpansionStringOverQ(a,minlen,maxlen)
    assert a[1] eq 1;
    s := "q";  t := s;
    n := 2;
    while qexp_display_len(s) lt minlen and n le #a do
        t := s;
        s cat:= LatexTerm(a[n],"q",n);
        n +:= 1;
    end while;
    return (qexp_display_len(s) le maxlen select s else t) cat "+\\\\cdots";
end function;

procedure write_header (outfile, outfp, cols)
    headfp := #outfile gt 0 select Open(outfile,"w") else outfp;
    labels := Join([r[1]:r in cols],":");
    types := Join([r[2]:r in cols],":");
    Puts(headfp,labels);  Puts(headfp,types); Puts(headfp,"");
    Flush(headfp);
end procedure;

/* list below created in sage using

from lmfdb.db_backend import db
for k in sorted(db.mf_newspaces.col_type.keys()):
    print '<"%s","%s">,'%(k,db.mf_newspaces.col_type[k])

but we want to leave id out
*/

newspaces_columns := [
<"AL_dims","jsonb">,
<"Nk2","integer">,
<"a4_dim","integer">,
<"a5_dim","integer">,
<"analytic_conductor","double precision">,
<"char_conductor","integer">,
<"char_degree","integer">,
<"char_is_real","boolean">,
<"char_orbit_index","smallint">,
<"char_orbit_label","text">,
<"char_order","integer">,
<"char_parity","smallint">,
<"char_values","jsonb">,
<"conrey_indexes","integer[]">,
<"cusp_dim","integer">,
<"dihedral_dim","integer">,
<"dim","integer">,
<"eis_dim","integer">,
<"eis_new_dim","integer">,
<"hecke_cutter_primes","integer[]">,
<"hecke_orbit_code","bigint">,
<"hecke_orbit_dims","integer[]">,
<"label","text">,
<"level","integer">,
<"level_is_prime","boolean">,
<"level_is_prime_power","boolean">,
<"level_is_square","boolean">,
<"level_is_squarefree","boolean">,
<"level_primes","integer[]">,
<"level_radical","integer">,
<"mf_dim","integer">,
<"mf_new_dim","integer">,
<"num_forms","smallint">,
<"plus_dim","integer">,
<"prim_orbit_index","smallint">,
<"relative_dim","integer">,
<"s4_dim","integer">,
<"sturm_bound","integer">,
<"trace_bound","integer">,
<"trace_display","numeric[]">,
<"traces","numeric[]">,
<"weight","smallint">,
<"weight_parity","smallint">
];

// cols set to true are computed by summing
gamma1_columns := [
<"Nk2","integer", false>,
<"a4_dim","integer", true>,
<"a5_dim","integer", true>,
<"analytic_conductor","double precision", false>,
<"cusp_dim","integer", true>,
<"dihedral_dim","integer", true>,
<"dim","integer", true>,
<"eis_dim","integer", true>,
<"eis_new_dim","integer", true>,
<"hecke_orbit_dims","integer[]", false>,
<"label","text", false>,
<"level","integer", false>,
<"level_is_prime","boolean",false>,
<"level_is_prime_power","boolean",false>,
<"level_is_square","boolean",false>,
<"level_is_squarefree","boolean",false>,
<"level_primes","integer[]", false>,
<"level_radical","integer", false>,
<"mf_dim","integer", true>,
<"mf_new_dim","integer", true>,
<"newspace_dims","integer[]", false>,
<"num_forms","integer", true>,
<"num_spaces","integer", false>,
<"s4_dim","integer", true>,
<"sturm_bound","integer", false>,
<"trace_bound","integer", false>,
<"trace_display","numeric[]", false>,
<"traces","numeric[]", false>,
<"weight","smallint", false>,
<"weight_parity","smallint", false>
];

hecke_traces_columns := [
<"hecke_orbit_code","bigint">,
<"n","integer">,
<"trace_an","numeric">
];

// For gamma1 cols constructed by summing/appending subspace columns, we only want to do this if the column is present in every newspace
// We detect missing data using Type eq MonStgElt (the columns we want to sum/append are not strings, but the null value "\\N" is).
function non_null (recs,c) return &and[Type(rec[c]) ne MonStgElt : rec in recs]; end function;

// infile format is N:k:o:time:dims:traces:hecke_fields:AL_signs:cutter_data  where dims is either an integer or list of integers giving dimensions of newforms,
//     traces is either a list or list of lists of at least 1000 integer traces, and cutter data is a list of primes (this may change)
//     if dims is a list, sum(dims) is the dimension of the space, and if traces is a list, sum(traces) gives the traces of the space
// hecke_fields,AL_signs,cutters are optional and as in mfdata
procedure FormatNewspaceData (infile, newspace_outfile, gamma1_outfile, trace_outfile, dimfile: conrey_labels:="", wt1_dims:="", Detail:=0, Jobs:=1, JobId:=0,SplitInput:=false)
    assert Jobs gt 0 and JobId ge 0 and JobId lt Jobs;
    if Jobs ne 1 then jobext := Sprintf("_%o",JobId); newspace_outfile cat:= jobext; gamma1_outfile cat:= jobext; trace_outfile cat:= jobext; end if;
    start:=Cputime();
    S := [Split(r,":"): r in Split(Read(dimfile),"\n")];
    S := [[StringToInteger(a):a in r]:r in S];
    DT := AssociativeArray();
    B := 0;
    for r in S do DT[[r[1],r[2],r[3]]]:=[r[4],r[5],r[6],r[7]]; B := Max(B,r[1]); end for;
    printf "Loaded %o records from dimension file %o in %os\n", #S, dimfile, Cputime()-start;
    start:=Cputime();
    if #wt1_dims gt 0 then
        S := [Split(r,":"): r in Split(Read(wt1_dims),"\n")]; // forms is N:1:o:[d1,d2,...]:[dihedral_dim,a4_dim,s4_dim,a5_dim]
        for r in S do
            key := [StringToInteger(r[i]):i in [1..3]];  assert key[2] eq 1;
            assert IsDefined(DT,key);
            DT[key] cat:= StringToIntegerArray(r[5]);
            assert #DT[key] ge 8;
        end for;
        printf "Loaded %o records from wt1 dims file %o in %o secs.\n", #S, wt1_dims, Cputime()-start;
        start:=Cputime();
    end if;
    if #conrey_labels gt 0 then
        S := [Split(r,":"):r in Split(Read(conrey_labels),"\n")]; // format is N:o:[n1,n2,...]:M:po:ord:deg:parity:isreal (list of conrey chars chi_N(n,*) in orbit o, M=cond, po=primi_orbit_index
        CT := AssociativeArray();
        CTN := [];
        for r in S do
            key := [StringToInteger(r[1]),StringToInteger(r[2])];
            CT[key] := <StringToIntegerArray(r[3])> cat <StringToInteger(r[i]):i in [4..9]>;
            if key[1] eq #CTN then assert key[2] eq CTN[key[1]]+1; CTN[key[1]] +:= 1; else assert key[1] eq #CTN+1 and key[2] eq 1; CTN[key[1]] := 1; end if;
        end for;
        printf "Loaded %o records from conrey label file %o in %o secs.\n", #Keys(CT), conrey_labels, Cputime()-start;
        start:=Cputime();
    end if;
    if SplitInput then infile cat:= Sprintf("_%o",JobId); end if;
    S := Split(Read(infile),"\n");
    printf "Loaded %o records from input file %o in %os\n", #S, infile, Cputime()-start;
    start := Cputime();
    outfp := Open(newspace_outfile,"w");
    g1outfp := Open(gamma1_outfile,"w");
    tracefp := Open(trace_outfile,"w");
    if JobId eq 0 then
        write_header (Jobs gt 1 select "mf_newspaces_header.txt" else "", outfp, newspaces_columns);
        write_header (Jobs gt 1 select "mf_gamma1_header.txt" else "", g1outfp, gamma1_columns);
        write_header (Jobs gt 1 select "mf_hecke_newspace_traces_header.txt" else "", tracefp, hecke_traces_columns);
    end if;
    rec := AssociativeArray();  g1rec := AssociativeArray();
    g1traces := [];  g1N := 0; g1k := 0;
    cnt := 0; g1cnt := 0; tcnt := 0;
    for s in S do
        N := StringToInteger(Substring(s,1,Index(s,":")-1));
        if not SplitInput and ((N-JobId) mod Jobs) ne 0 then continue; end if;
        for c in newspaces_columns do rec[c[1]] := "\\N"; end for;
        r := Split(s,":");
        k := StringToInteger(r[2]); o := StringToInteger(r[3]);
        if #r ge 5 then
            dims := eval(r[5]);
            if Type(dims) eq RngIntElt then dim := dims; dims := -1; num := -1; else dim := sum(dims); num := #dims; end if;
        else
            dims := -1; dim := -1; num := -1;
        end if;
        if #r ge 6 then
            traces := eval(r[6]);
            if #traces eq 0 then
                assert dim le 0; straces := traces;
            else
                if Type(traces[1]) eq RngIntElt then
                    straces := traces; traces := -1;
                else
                    assert #traces eq num and [t[1]:t in traces] eq dims;
                    assert #{#t:t in traces} eq 1;
                    straces := [&+[traces[i][j]:i in [1..num]]:j in [1..#traces[1]]];
                end if;
            end if;
            num_traces := #straces;
        else
            traces := -1; straces := -1; num_traces := -1;
        end if;
        P := PrimeDivisors(N);
        label := NewspaceLabel(N,k,o);
        rec["label"] := label;
        rec["level"] := N;
        rec["level_is_prime"] := IsPrime(N) select 1 else 0;
        rec["level_is_prime_power"] := (N gt 1 and IsPrimePower(N)) select 1 else 0;
        rec["level_is_square"] := IsSquare(N) select 1 else 0;
        rec["level_is_squarefree"] := IsSquarefree(N) select 1 else 0;
        rec["level_primes"] := P;
        rec["level_radical"] := prod(P);
        rec["weight"] := k;
        rec["weight_parity"] := (-1)^k;
        rec["Nk2"] := N*k*k;
        rec["analytic_conductor"] := AnalyticConductor(N,k);
        rec["char_orbit_index"] := o;
        rec["char_orbit_label"] := Base26Encode(o-1);
        cr := o gt 1 select CT[[N,o]] else <[1],1,1,1,1,1,1>;
        code := HeckeOrbitCode(N,k,o,1);
        rec["hecke_orbit_code"] := code;
        rec["conrey_indexes"] := cr[1];
        rec["char_conductor"] := cr[2];
        rec["prim_orbit_index"] := cr[3];
        rec["char_order"] := cr[4];
        rec["char_degree"] := cr[5];
        rec["char_parity"] := cr[6];
        rec["char_is_real"] := cr[7];
        n := cr[4];
        u := UnitGenerators(N);
        if o eq 1 then
            v := [Integers()|n : x in u];
        else
            v := [Integers()|n*a : a in ConreyCharacterAngles(N,CT[[N,o]][1][1],u)];
        end if;
        rec["char_values"] := <N,n,u,v>;
        sdims := DT[[N,k,o]];
        dS := sdims[1];  dE := sdims[2];  dNS := sdims[3]; dNE := sdims[4]; dM:=dS+dE; dNM:= dNS+dNE;
        assert dS ge 0 and dE ge 0 and dNS ge 0 and dNE ge 0;
        if dim ge 0 then assert dim eq dNS; end if;
        if dNS eq 0 then num := 0; dims :=[]; traces := []; num_traces := 0; straces :=[]; trace_bound := 1; end if;
        rec["cusp_dim"] := dS;
        rec["dim"] := dNS;
        rec["relative_dim"] := ExactQuotient(dNS,cr[5]);
        rec["eis_dim"] := dE;
        rec["eis_new_dim"] := dNE;
        rec["mf_dim"] := dM;
        rec["mf_new_dim"] := dNM;
        if k eq 1 then
            assert #sdims ge 8; // we expect wt1 dihedral/a4/s4/a5 dim data to have been loaded into DT from wt1_dims
            rec["dihedral_dim"] := sdims[5];
            rec["a4_dim"] := sdims[6];
            rec["s4_dim"] := sdims[7];
            rec["a5_dim"] := sdims[8];
        end if;
        if num_traces gt 0 then
            assert straces[1] eq rec["dim"];
            rec["traces"] := straces;
            rec["trace_display"] := [straces[2],straces[3],straces[5],straces[7]];
            for i := 1 to 1000 do Puts(tracefp,Sprintf("%o:%o:%o",code,i,straces[i])); end for;
            Flush(tracefp);
            tcnt +:= 1000;
        end if;
        if num ge 0 then
            assert dNS eq sum(dims);
            rec["num_forms"] := num;
            rec["hecke_orbit_dims"] := dims;
            trace_bound := 0;
            if num gt 0 then
                while trace_bound le num_traces and #{traces[n][1..trace_bound]:n in [1..num]} lt num do trace_bound +:= 1; end while;
            end if;
            if num_traces gt 0 and trace_bound gt num_traces then
                print "*** Error: unable to determine trace bound for space %o:%o:%o:%o, tr(a_n) for n <= %o are not distinct (continuing) ***\n", N, k, o, dims, num_traces;
            else
                rec["trace_bound"] := trace_bound;
            end if;
            if k gt 1 and o eq 1 and #dims gt 0 then
                AL_signs := eval(r[7]);
                assert #AL_signs eq #dims;
                AL_dims := [];
                S := Set(P);
                for s in Subsets(S) do
                    t := S diff s;
                    ALsub := [dims[i] : i in [1..#dims] | &and[(a[2] eq 1 and a[1] in s) or (a[2] eq -1 and a[1] in t):a in AL_signs[i]]];
                    if #ALsub gt 0 then Append(~AL_dims,<[[p, p in s select 1 else -1]:p in P],sum(ALsub),#ALsub>); end if;
                end for;
                rec["AL_dims"] := AL_dims;
                rec["plus_dim"] := sum([a[2]:a in AL_dims|prod([Integers()|b[2]:b in a[1]]) eq 1]);
            end if;
            if #r ge 9 then
                cutters := eval(r[9]);
                if #cutters gt 0 then
                    assert #cutters le num; // don't require cutters to be present for every newform
                    assert #{[cc[1]:cc in c] :c in cutters } eq 1;
                    rec["hecke_cutter_primes"] := [cc[1] : cc in cutters[1]];
                end if;
            end if;
        end if;
        rec["sturm_bound"] := SturmBound(N,k);
        if g1N eq 0 then
            assert o eq 1;
            g1N := N; g1k := k; g1sscnt := 1;
            for c in gamma1_columns do g1rec[c[1]] := "\\N"; end for;
            g1rec["label"] := Sprintf("%o.%o",N,k);
            for c in ["level", "level_is_prime", "level_is_prime_power", "level_is_square", "level_is_squarefree", "level_primes", "level_radical", "weight", "weight_parity", "Nk2","analytic_conductor"] do
                g1rec[c] := rec[c];
            end for;
            for c in gamma1_columns do if c[3] and non_null([rec],c[1]) then g1rec[c[1]] := rec[c[1]]; end if; end for; 
            if non_null([rec],"hecke_orbit_dims") then g1rec["hecke_orbit_dims"] := rec["hecke_orbit_dims"]; end if;
            g1rec["traces"] := num_traces gt 0 select [rec["traces"]] else (num_traces eq 0 select [] else "\\N");
            g1rec["newspace_dims"] := [rec["dim"]];
            g1rec["num_spaces"] := rec["dim"] gt 0 select 1 else 0;
            g1rec["sturm_bound"] := Floor(k*N^2*prod([Rationals()|(1-1/p^2):p in PrimeDivisors(N)])/12);
        end if;
        assert N eq g1N and k eq g1k; // input must be sorted by N,k,o
        if o gt 1 then
            for c in gamma1_columns do if c[3] then if non_null([rec,g1rec],c[1]) then g1rec[c[1]] +:= rec[c[1]]; else g1rec[c[1]] := "\\N"; end if; end if; end for; 
            // only store hecke_orbit_dims for gamma1 if we have them for every subspace
            if non_null([g1rec,rec],"hecke_orbit_dims") then g1rec["hecke_orbit_dims"] cat:= rec["hecke_orbit_dims"]; else g1rec["hecke_orbit_dims"] := "\\N"; end if;
            if non_null([g1rec],"traces") then if num_traces gt 0 then Append(~g1rec["traces"],rec["traces"]); else if num_traces lt 0 then g1rec["traces"] := "\\N"; end if; end if; end if;
            Append(~g1rec["newspace_dims"],rec["dim"]);
            g1rec["num_spaces"] +:= rec["dim"] gt 0 select 1 else 0;
            g1sscnt +:= 1;
        end if;
        if o eq CTN[N] then
            assert g1sscnt eq o; // Verify that we have seen every space
            if k gt 1 then
                assert DimensionCuspFormsGamma1(N,k) eq g1rec["cusp_dim"];
                assert DimensionNewCuspFormsGamma1(N,k) eq g1rec["dim"];
            end if;
            assert &+g1rec["newspace_dims"] eq g1rec["dim"];
            if non_null([g1rec],"traces") then
                if #g1rec["traces"] eq 0 then
                    assert g1rec["dim"] eq 0;
                    assert g1rec["num_spaces"] eq 0;
                    g1rec["hecke_orbit_dims"] := [];
                else
                    traces := g1rec["traces"];
                    assert g1rec["num_spaces"] eq #traces;
                    assert sum([t[1]:t in traces]) eq g1rec["dim"];
                    num_traces := Min([#t:t in traces]);
                    assert num_traces ge 1000;
                    trace_bound := 0; while #{traces[n][1..trace_bound]:n in [1..#traces]} lt #traces and trace_bound le num_traces do trace_bound +:= 1; end while;
                    if trace_bound gt num_traces then
                        print "*** Warning! Unable to determine trace bound for Gamma1 space %o:%o, tr(a_n) for n <= %o are not distinct ***\n", N, k, num_traces;
                    else
                        g1rec["trace_bound"] := trace_bound;
                    end if;
                    g1rec["traces"] := [&+[t[i]:t in traces]:i in [1..num_traces]];
                    g1rec["trace_display"] := [t[2],t[3],t[5],t[7]] where t := g1rec["traces"];
                    if non_null([g1rec],"hecke_orbit_dims") then
                        assert sum(g1rec["hecke_orbit_dims"]) eq g1rec["dim"];
                        assert #g1rec["hecke_orbit_dims"] eq g1rec["num_forms"];
                    end if;
                end if;
            end if;
            assert Sort([x:x in Keys(g1rec)]) eq [t[1]: t in gamma1_columns];
            // copy text fields as is (do not trim spaces!), and use curly braces in arrays
            str := bracket(Join([t[2] eq "text" select g1rec[t[1]] else (t[2][#t[2]] eq "]" select curly(s) else s where s:=sprint(g1rec[t[1]])):t in gamma1_columns],":"));
            if Detail gt 0 then print str; else if Detail ge 0 then printf "%o (%os, %oMB)\n", label, Cputime()-start, Memory(); end if; end if;
            Puts(g1outfp,str);  Flush(g1outfp);
            g1cnt +:= 1;
            g1N := 0;  g1k:= 0;
        end if;
        assert Sort([x:x in Keys(rec)]) eq [t[1]: t in newspaces_columns];
        // copy text fields as is (do not trim spaces!), and use curly braces in arrays
        str := bracket(Join([t[2] eq "text" select rec[t[1]] else (t[2][#t[2]] eq "]" select curly(s) else s where s:=sprint(rec[t[1]])):t in newspaces_columns],":"));
        if Detail gt 0 then print str; else if Detail ge 0 then printf "%o (%os, %oMB)\n", label, Cputime()-start, Memory(); end if; end if;
        Puts(outfp,str);  Flush(outfp);
        cnt +:= 1;
    end for;
    printf "Wrote %o records to %o and %o records to %o and %o records to %o in %o secs\n", cnt, newspace_outfile, g1cnt, gamma1_outfile, tcnt, trace_outfile, Cputime()-start;
end procedure;

procedure LookupFields (infile,field_labels:Jobs:=1,JobId:=0,SplitInput:=false)
    R<x>:=PolynomialRing(Integers());
    S:=Split(Read(field_labels),"\n");  // format is coeffs:label
    start:=Cputime();
    FieldTable:=AssociativeArray();
    for s in S do r:=Split(s,":"); FieldTable[eval(r[1])]:= r[2]; end for;
    printf "Loaded %o records from field label file %o in %o secs.\n", #Keys(FieldTable), field_labels, Cputime()-start;
    start:=Cputime();
    if SplitInput then infile cat:= Sprintf("_%o",JobId); end if;
    S := Split(Read(infile),"\n");
    printf "Loaded %o records from input file %o in %o secs.\n", #S, infile, Cputime()-start;
    OT := AssociativeArray();
    unknown_fields := {};
    nopolredabs_fields := {};
    cnt := 0;  unknown_cnt := 0;  nopolredabs_cnt := 0;
    for i:=1 to #S do
        if not SplitInput and ((i-JobId) mod Jobs) ne 0 then continue; end if;
        r := <eval(a):a in Split(S[i],":")>;
        N := r[1]; k := r[2]; o := r[3]; dims := r[5];
        assert #r ge 13;
        for n := 1 to #r[8] do 
            field_poly := r[8][n];
            assert #field_poly eq dims[n]+1;
            if r[13][n] eq 1 then
                if IsDefined(FieldTable,field_poly) then
                    nf_label := FieldTable[field_poly];
                    assert nf_label eq "\\N" or #Split(nf_label,".") eq 4;
                else
                    nf_label := "\\N";
                    if not field_poly in unknown_fields then
                        Include(~unknown_fields,field_poly);
                        PrintFile("unknown_fields.txt",strip(Sprintf("%o",field_poly)));
                        unknown_cnt +:= 1;
                    end if;
                end if;
            else
                if not field_poly in nopolredabs_fields then
                    Include(~nopolredabs_fields,field_poly);
                    PrintFile("nopolredabs_fields.txt",field_poly); 
                    nopolredabs_cnt +:= 1;
                end if;
            end if;
        end for;
        m := #[d:d in dims|d eq 1];
        for n := m+1 to m+#r[10] do
            nn := n-m;
            assert r[8][n] eq r[10][nn][1];
        end for;
    end for;
    if unknown_cnt gt 0 then printf "Appended %o unknown polredabs field polys to unknown_fields.txt\n", unknown_cnt; end if;
    if nopolredabs_cnt gt 0 then printf "Appended %o no polredabs field polys to nopolredabs_fields.txt\n", nopolredabs_cnt; end if;
end procedure;


/*
List below produced in sage using:
    
from lmfdb import db
sage: for k in sorted(db.mf_newforms.col_type.keys()):
     print '<"%s","%s",%s>,'%(k,db.mf_newforms.col_type[k],"true" if db.mf_newspaces.col_type.get(k) else "false")
        
but note true/false for label and space_label need to be swapped, and we want to leave out id
*/
newforms_columns := [
<"Nk2","integer", true>,
<"analytic_conductor","double precision", true>,
<"analytic_rank","smallint", false>,
<"analytic_rank_proved","boolean",false>,
<"artin_degree","integer", false>,
<"artin_field","numeric[]", false>,
<"artin_field_label","text", false>,
<"artin_image","text", false>,
<"atkin_lehner_eigenvals","integer[]", false>,
<"atkin_lehner_string","text", false>,
<"char_conductor","integer", true>,
<"char_degree","integer", true>,
<"char_is_minimal","boolean", true>,
<"char_is_real","boolean", true>,
<"char_orbit_index","smallint", true>,
<"char_orbit_label","text", true>,
<"char_order","integer", true>,
<"char_parity","smallint", true>,
<"char_values","jsonb",true>,
<"cm_discs","integer[]", false>,
<"conrey_indexes","integer[]", true>,
<"dim","integer", false>,
<"embedded_related_objects","text[]", false>,
<"field_disc","numeric",false>,
<"field_disc_factorization","numeric[]",false>,
<"field_poly","numeric[]", false>,
<"field_poly_is_cyclotomic","boolean", false>,
<"field_poly_is_real_cyclotomic","boolean", false>,
<"field_poly_root_of_unity","integer", false>,
<"fricke_eigenval","smallint", false>,
<"has_non_self_twist","smallint",false>,
<"hecke_cutters","jsonb", false>,
<"hecke_orbit","integer", false>,
<"hecke_orbit_code","bigint", false>,
<"hecke_ring_generator_nbound","integer",false>,
<"hecke_ring_index","numeric", false>,
<"hecke_ring_index_factorization","numeric[]", false>,
<"hecke_ring_index_proved","boolean", false>,
<"inner_twists","integer[]", false>,
<"inner_twist_count","integer", false>,
<"is_cm","boolean", false>,
<"is_polredabs","boolean", false>,
<"is_rm","boolean", false>,
<"is_self_dual","boolean", false>,
<"is_self_twist","boolean", false>,
<"is_twist_minimal","boolean", false>,
<"label","text", false>,
<"level","integer", true>,
<"level_is_prime","boolean",true>,
<"level_is_prime_power","boolean",true>,
<"level_is_square","boolean",true>,
<"level_is_squarefree","boolean",true>,
<"level_primes","integer[]", true>,
<"level_radical","integer", true>,
<"minimal_twist","text", false>,
<"nf_label","text", false>,
<"prim_orbit_index","smallint", true>,
<"projective_field","numeric[]", false>,
<"projective_field_label","text", false>,
<"projective_image","text", false>,
<"projective_image_type","text", false>,
<"qexp_display","text", false>,
<"related_objects","text[]", false>,
<"relative_dim", "integer", false>,
<"rm_discs","integer[]", false>,
<"sato_tate_group", "text", false>,
<"self_twist_discs","integer[]", false>,
<"self_twist_type","smallint", false>,
<"space_label","text", true>,
<"trace_display","numeric[]", false>,
<"trace_hash","bigint", false>,
<"trace_moments","numeric[]", false>,
<"trace_zratio","numeric", false>,
<"traces","numeric[]", false>,
<"weight","smallint", true>,
<"weight_parity","smallint", true>
];

hecke_nf_columns := [
<"an","jsonb", false>,
<"ap","jsonb", false>,
<"char_orbit_index","smallint", true>,
<"field_poly","numeric[]", false>,
<"hecke_orbit_code","bigint", true>,
<"hecke_ring_character_values","jsonb", false>,
<"hecke_ring_cyclotomic_generator","integer", false>,
<"hecke_ring_denominators","numeric[]", false>,
<"hecke_ring_inverse_denominators","numeric[]", false>,
<"hecke_ring_inverse_numerators","numeric[]", false>,
<"hecke_ring_numerators","numeric[]", false>,
<"hecke_ring_power_basis","boolean", false>,
<"hecke_ring_rank","integer", false>,
<"label","text", false>,
<"level","integer", true>,
<"maxp","integer", false>,
<"weight","smallint", true>
];

hecke_lpolys_columns := [
<"hecke_orbit_code","bigint">,
<"lpoly","numeric[]">,
<"p","integer">
];


/*
 Format of infile is N:k:i:t:D:T:A:F:C:E:cm:tw:pra:zr:mm:h:X:sd:eap where

 1) N = level, a positive integer
 2) k = weight, a positive integer (for .m.txt files, k > 1)
 3) i = character orbit of chi (Galois orbits of Dirichlet characters chi of modulus N are lex-sorted by order and then by trace vectors [tr(chi(n)) for n in [1..N]], taking traces from Q(chi) to Q; the first orbit index is 1, corresponding to the trivial character, the second orbit will correspond to a quadratic character).
 4) t = time in secs to compute this line of data
 5) D = sorted list of dimensions [d1,d2,...] of Galois stable subspaces of S_k^{new}(N,chi), ordered by dimension
 6) T = lex-sorted list of trace vectors [[tr(a_1),...tr(a_n)],...] for Galois conjugacy classes of eigenforms f corresponding to the subspaces listed in D, traces are from the coefficient field of the form down to Q (note that lex-sorting trace vectors sorts subspaces by dimension because tr(a_1)=tr(1) is the degree of the coefficient field)
 7) A = Atkin-Lehner signs (empty list if chi is not the trivial character (i.e. i=1)) [[<p,sign> for p in Divisors(N)],...], one list of Atkin-Lehner signs for each subspace listed in D.
 8) F = Hecke field polys [[f0,f1,...,1],...] list of coeffs (constant coeff first), one list for each subspace listed in D of dimension up to the degree bound (currently 20); note that F[n] corresponds to the space D[n] but F may be shorter than D
 9) C = Hecke cutters [[<p,[g0,g1,...,1]>,...],...] list of minimal lists of coefficients of kernel polys g_p in T_p sufficient to distinguish all the subspaces listed in D (i.e. the ith form is the unique form lying in the kernel of g_p(T_p) for all the tuples <p,coeffs(g_p)> in the ith list)
10) E = Hecke Eigenvalue data [<g,b,c,d,a,x,m>,...] list of 7-tuples of Hecke eigenvalue data for each subspace listed in D of dimension greater than 1 up to the degree bound where:
      1) g is a list of coefficients of a polredbestified field poly for the Hecke field K (should match entry in F),
      2) b is a list of lists of rationals specifying a basis for the Hecke ring R:=Z[a_n] in terms of the power basis for g
      3) c is an integer that divides the index [O_K:R] of the Hecke ring R in the ring of integers O_K of the Hecke field
      4) d is a pair <disc,fac> where disc is the discriminant of O_K (0 if not known) and fac=[<p,e>,...] is its factorization.
      5) a is a list of lists of integers encoding eigenvalues in terms of the basis b
      6) x is a pair <u,v> where u lists integers generating (Z/NZ)* and v lists of values of chi on u in basis b
      7) m is the least integer such that the coefficients a_1,...,a_m generate the Hecke ring (as a ring)
11) cm = list of pairs <proved,discs> where proved=0,1 and discs is a list of 0, 1, or 3 fundamental discriminants (for k > 1 there is at most 1 and it is a negative discriminant), one pair for each subspace listed in D
12) tw = list of lists of quadrauples <proved,n,m,o> where proved=0,1, n >=1 is a multiplicity, and m and o identify a Galois orbit of a characters [phi] of modulus m for which the corresponding form admits n distinct non-trivial inner-twist by characters in xi in [phi], one list for each subspace up to degree bound. All self-twists are guaranteed to be included, but quadruples with proved=0 could in principal be false positives.
13) pra = list of boolean values (0 or 1) such that pra[i] is 1 if F[i] is the polredabs polynomial for the Hecke field
14) zr = list of proportions of zero a_p over primes p < 2^13 (decimal number), one for each subspace
15) mm = list of list of moments of normalized a_p over primes p < 2^13 (decimal numbers), one for each subspace
16) h = list of trace hashes (linear combination of tr(a_p) over p in [2^12,2^13] mod 2^61-1), one for each subspace of dimension up to the degree bound (not yet present for weight 1)
17) X = list of pairs <u,v>, one for each entry in F, where u is a list of integer generators for (Z/NZ)* and v is a list of lists of rationals specifying corresponding values of chi in the Hecke field in terms of the power basis for F[i].
18) sd = list of boolean values (0,1), one for each subspace in D indicating whether the subspace is self-dual (meaning the a_n are real-valued)
19) eap = list of lists of lists of embedded ap's, one for each subspace in D of dimension greater than the degree bound; for trivial character these are lists of real numbers, otherwise lists of pairs of real numbers encoding real and imaginary parts (the latter 0 if a_n is real).  For each subspace of dimension d there are d lists of embedded ap's [a_2,a_3,...]
*/

procedure FormatNewformData (infile, outfile_prefix, outfile_suffix: Detail:=0, Jobs:=1, JobId:=0, conrey_labels:="", artin_reps:="", SplitInput:=false)
    assert Jobs gt 0 and JobId ge 0 and JobId lt Jobs;
    if not "." in outfile_suffix then outfile_suffix cat:= ".txt"; end if;
    if Jobs ne 1 then outfile_suffix cat:= Sprintf("_%o",JobId); end if;
    newform_outfile := outfile_prefix cat "mf_newforms_" cat outfile_suffix;
    hecke_outfile := outfile_prefix cat "mf_hecke_nf_" cat outfile_suffix;
    trace_outfile := outfile_prefix cat "mf_hecke_traces_" cat outfile_suffix;
    lpoly_outfile := outfile_prefix cat "mf_hecke_lpolys_" cat outfile_suffix;
    ConreyTable:=AssociativeArray();
    if conrey_labels ne "" then
        start:=Cputime();
        S := Split(Read(conrey_labels),"\n");  // format is N:o:[n1,n2,...]:conductor:prim_index:order:deg:parity:isreal:isminimal (use conrey_XXX.txt)
        for s in S do r:=Split(s,":"); ConreyTable[[StringToInteger(r[1]),StringToInteger(r[2])]] := r[3]; end for;
        printf "Loaded %o records from conrey label file %o in %o secs.\n", #Keys(ConreyTable), conrey_labels, Cputime()-start;
    end if;
    start:=Cputime();
    R<x>:=PolynomialRing(Integers());
    S:=Split(Read("lmfdb_nf_labels.txt"));  // format is coeffs:label
    FieldTable:=AssociativeArray();
    for s in S do r:=Split(s,":"); FieldTable[eval(r[1])]:= r[2]; end for;
    printf "Loaded %o records from lmfdb_nf_labels.txt in %o secs.\n", #Keys(FieldTable), Cputime()-start;
    RankTable:=AssociativeArray();  start := Cputime();
    b,S := ReadTest("mf_ranks.txt");  // format is label:rank:proved
    if b then
        for s in Split(S) do r:=Split(s,":"); RankTable[r[1]]:= [StringToInteger(r[2]),StringToInteger(r[3])]; end for;
        printf "Loaded %o records from mf_ranks.txt in %o secs.\n", #Keys(RankTable), Cputime()-start;
    end if;
    ArtinTable:=AssociativeArray();  start := Cputime();
    if artin_reps ne "" then
        S := Read(artin_reps);  // format is level:1:char_orbit:hecke_orbit:label:artin_label:discs:ptype:pname:ppoly:min_twist_label:deg:id:poly:tzratio,tzmoments:thahs
        for s in Split(S) do r:=Split(s,":"); ArtinTable[r[5]]:= r; end for;
        printf "Loaded %o records from Artin rep file %o in %o secs.\n", #Keys(ArtinTable), artin_reps, Cputime()-start;
    end if;
    InnerTwistTable := AssociativeArray();  start := Cputime();
    b,S := ReadTest("mftwists_inner.txt");   // format is source:target:chars:mults (ignore records with source != target)
    if b then
        for s in Split(S) do r:=Split(s,":"); if r[1] eq r[2] then InnerTwistTable[r[1]] := [r[3],r[4],r[5]]; end if; end for;
        printf "Loaded %o records from mftwists_inner.txt in %o secs.\n", #Keys(InnerTwistTable), Cputime()-start;
    end if;
    MinimalTwistTable := AssociativeArray();  start := Cputime();
    b,S := ReadTest("mftwists_minimal.txt");  // format is source:target
    if b then
        for s in Split(S) do r:=Split(s,":"); MinimalTwistTable[r[2]] := r[1]; end for;
        printf "Loaded %o records from mftwists_minimal.txt in %o secs.\n", #Keys(MinimalTwistTable), Cputime()-start;
    end if;
    RelatedObjects:=AssociativeArray();  start := Cputime();
    b,S := ReadTest("mf_related_objects.txt");  // format is label:URL
    if b then
        for s in Split(S) do r:=Split(s,":"); if IsDefined(RelatedObjects,r[1]) then Append(~RelatedObjects[r[1]],r[2]); else RelatedObjects[r[1]] := [r[2]]; end if; end for;
        printf "Loaded %o records from mf_related_objects.txt in %o secs.\n", #Keys(RelatedObjects), Cputime()-start;
    end if;
    start := Cputime();
    if SplitInput then infile cat:= Sprintf("_%o",JobId); end if;
    S := Split(Read(infile));
    printf "Loaded %o records from input file %o in %o secs.\n", #S, infile, Cputime()-start;
    start:=Cputime();
    newform_fp := Open(newform_outfile,"w");
    hecke_fp := Open(hecke_outfile,"w");
    trace_fp := Open(trace_outfile,"w");
    lpoly_fp := Open(lpoly_outfile,"w");
    if JobId eq 0 then
        write_header (Jobs gt 1 select "mf_newforms_header.txt" else "", newform_fp, newforms_columns);
        write_header (Jobs gt 1 select "mf_hecke_nf_header.txt" else "", hecke_fp, hecke_nf_columns);
        write_header (Jobs gt 1 select "mf_hecke_traces_header.txt" else "", trace_fp, hecke_traces_columns);
        write_header (Jobs gt 1 select "mf_hecke_lpolys_header.txt" else "", lpoly_fp, hecke_lpolys_columns);
    end if;
    OT := AssociativeArray();
    unknown_fields := {};
    cnt := 0; trcnt := 0; hnfcnt := 0; lpcnt := 0; unknown_cnt := 0;
    rec := AssociativeArray();
    rechnf := AssociativeArray();
    RCP := AssociativeArray();  RCPI := AssociativeArray();
    LPP := PrimesInInterval(1,100);
    for s in S do
        N := StringToInteger(Substring(s,1,Index(s,":")-1));
        if not SplitInput and ((N-JobId) mod Jobs) ne 0 then continue; end if;
        for c in newforms_columns do rec[c[1]] := "\\N"; end for;
        for c in hecke_nf_columns do rechnf[c[1]] := "\\N"; end for;
        r := <eval(a):a in Split(s,":")>;
        assert #r ge 18;
        assert #r[5] eq #r[6];
        assert #r[5] eq #r[11];
        assert #r[5] eq #r[18];
        if r[3] eq 1 then assert #r[5] eq #r[7]; end if;
        assert #r[8] eq #r[13];
        N := r[1]; k := r[2]; o := r[3]; dims := r[5];
        rec["Nk2"]:= N*k*k;
        rec["level"] := N;
        rechnf["level"] := N;
        P := PrimeDivisors(N);
        rec["level_is_prime"] := IsPrime(N) select 1 else 0;
        rec["level_is_prime_power"] := (N gt 1 and IsPrimePower(N)) select 1 else 0;
        rec["level_is_square"] := IsSquare(N) select 1 else 0;
        rec["level_is_squarefree"] := IsSquarefree(N) select 1 else 0;
        rec["level_primes"] := P;
        rec["level_radical"] := prod(P);
        rec["weight"] := k;
        rechnf["weight"] := k;
        rec["weight_parity"] := (-1)^k;
        rec["char_orbit_index"] := o;
        rechnf["char_orbit_index"] := o;
        rec["analytic_conductor"] := AnalyticConductor(N,k);
        if o gt 1 and not IsDefined(OT,N) then G,T := CharacterOrbitReps(N:RepTable); OT[N] := <G,T>; end if;
        chi := o eq 1 select DirichletGroup(N)!1 else OT[N][1][o];
        M := Conductor(chi);
        if o gt 1 and not IsDefined(OT,M) then G,T := CharacterOrbitReps(M:RepTable); OT[M] := <G,T>; end if;
        rec["char_conductor"] := M;
        rec["prim_orbit_index"] := o eq 1 select 1 else OT[M][2][AssociatedPrimitiveCharacter(chi)];
        rec["space_label"] := NewspaceLabel(N,k,o);
        rec["char_orbit_label"] := Base26Encode(o-1);
        rec["char_order"] := Order(chi);
        rec["char_is_minimal"] := IsMinimal(chi) select 1 else 0;
        if o gt 1 and not IsDefined(ConreyTable,[N,o]) then
            t := Cputime();
            ConreyTable[[N,o]] := sprint(ConreyIndexes(chi));
            printf "Generating Conrey labels for character orbit %o of modulus %o in %.3os\n", o, N, Cputime()-t;
        end if;
        rec["conrey_indexes"] := o eq 1 select "[1]" else ConreyTable[[N,o]];
        rec["char_parity"] := Parity(chi);
        rec["char_is_real"] := IsReal(chi) select 1 else 0;
        rec["char_degree"] := Degree(chi);
        n := Order(chi);
        u := UnitGenerators(chi);
        if o eq 1 then
            v := [Integers()|n : x in u];
        else
            v := [Integers()|n*a : a in ConreyCharacterAngles(N,clist[1],u)] where clist := atoii(ConreyTable[[N,o]]);
        end if;
        rec["char_values"] := <N,n,u,v>;
        m := #[d:d in dims|d eq 1];
        for n := 1 to #dims do
            dim := dims[n];
            // clear columns that are not space invariant
            for c in newforms_columns do if not c[3] then rec[c[1]] := "\\N"; end if; end for;
            for c in hecke_nf_columns do if not c[3] then rechnf[c[1]] := "\\N"; end if; end for;
            rec["hecke_orbit"] := n;
            rec["dim"] := dim;
            rec["relative_dim"] := ExactQuotient(dims[n],Degree(chi));
            label := NewformLabel(N,k,o,n);
            rec["label"] := label;
            rechnf["label"] := rec["label"];
            code := HeckeOrbitCode(N,k,o,n);
            rec["hecke_orbit_code"] := code;
            rechnf["hecke_orbit_code"] := code;
            rec["trace_display"] := [r[6][n][2],r[6][n][3],r[6][n][5],r[6][n][7]];
            tr := r[6][n];
            rec["traces"] := tr;
            assert #tr ge 1000;
            // only put 1000 traces into mf_hecke_traces even when we have more
            for i := 1 to 1000 do Puts(trace_fp,Sprintf("%o:%o:%o",code,i,tr[i])); end for;
            trcnt +:= 1000;
            Flush(trace_fp);
            if o eq 1 then
                rec["atkin_lehner_eigenvals"] := r[7][n];
                rec["fricke_eigenval"] := prod([Integers()|a[2]:a in r[7][n]]);
                rec["atkin_lehner_string"] := #r[7][n] gt 0 select &cat[a[2] eq 1 select "+" else "-" : a in r[7][n]] else "";
            end if;
            if IsDefined(RankTable,label) and RankTable[label][1] ge 0 then
                rec["analytic_rank"] := RankTable[label][1];
                rec["analytic_rank_proved"] := RankTable[label][2];
            else
                printf "Warning: no record for newform %o found in RankTable\n", label;
            end if;
            assert r[11][n][1] eq 1;  // self twists should always be proved (and can be derived from inner twists if not)
            std := Sort(r[11][n][2],func<a,b|Abs(a)-Abs(b)>);
            assert #std in [0,1,3] and (#std lt 3 or k eq 1);
            rec["cm_discs"] := [d:d in std|d lt 0];
            rec["rm_discs"] := [d:d in std|d gt 0];
            rec["self_twist_discs"] := rec["cm_discs"] cat rec["rm_discs"];
            rec["is_self_twist"] := #std gt 0 select 1 else 0; 
            rec["is_cm"] := #[d:d in std|d lt 0] gt 0 select 1 else 0; 
            rec["is_rm"] := #[d:d in std|d gt 0] gt 0 select 1 else 0;
            if #std eq 3 then rec["self_twist_type"] := 3; else if #std eq 0 then rec["self_twist_type"] := 0; else rec["self_twist_type"] := std[1] lt 0 select 1 else 2; end if; end if;
            if #InnerTwistTable gt 0 then
                if IsDefined(InnerTwistTable,label) then
                    assert Set(std) eq Set(StringToIntegerArray(InnerTwistTable[label][3]));
                else
                    printf "Warning: no record for newform %o found in InnerTwistTable\n", label;
                end if;
            end if;
            itproved := false;
            rec["inner_twist_count"] := -1;
            rec["has_non_self_twist"] := -1;
            if n le #r[12] then
                rec["has_non_self_twist"] := #r[12][n] gt 0 select 1 else 0;
                for it in r[12][n] do if not IsDefined(OT,it[3]) then G,T := CharacterOrbitReps(it[3]:RepTable);  OT[it[3]] := <G,T>; end if; end for;
                rec["inner_twists"] := [<1,1,1,1,1,1,1>] cat
                                       [<r[11][n][1],1,Modulus(psi),CharacterOrbit(psi),Parity(psi),2,d> where psi:=KroneckerCharacter(d,Rationals()) : d in rec["self_twist_discs"]] cat
                                       [<it[1],it[2],it[3],it[4],Parity(psi),Order(psi),0> where psi:=OT[it[3]][1][it[4]] : it in r[12][n]];
                rec["inner_twist_count"] := sum([t[2]:t in rec["inner_twists"]]);
                if #InnerTwistTable gt 0 then
                    if IsDefined(InnerTwistTable,label) then
                        z := InnerTwistTable[label];
                        psis := [SplitCharacterOrbitLabel(s): s in StringToStrings(z[1])];  ms := atoii(z[2]);
                        assert Set([[x[2],x[3],x[4]]:x in rec["inner_twists"]]) eq Set([[ms[i],psis[i][1],psis[i][2]]:i in [1..#ms]]);
                        if #[it:it in rec["inner_twists"]|it[1] ne 1] gt 0 then print "Proved previously unproved inner twist!"; end if;
                        rec["inner_twists"] := [<1,a[2],a[3],a[4],a[5],a[6],a[7]>:a in rec["inner_twists"]];
                        itproved := true;
                    else
                        printf "Warning: no record for newform %o found in InnerTwistTable\n", label;
                    end if;
                end if;
                // attempt to prove unproved inner twists using the fact that the automorphism group of the Hecke field must contain a subgroup
                // of cardinality equal to the number of inner twists divided by the number of self twists
                // No longer needed since we provably compute all twists
                /*
                if not itproved and n le #r[8] then
                    st := 1+#rec["self_twist_discs"];
                    itm := sum([a[2]:a in rec["inner_twists"]|a[1] eq 1]);
                    itM := rec["inner_twist_count"];
                    assert IsDivisibleBy(itM,st);
                    if itm gt st and itm lt itM then
                        printf "Attempting to prove inner twists for newform %o:%o:%o:%o...", N,k,o,n;
                        t := Cputime();
                        auts := #Automorphisms(NumberField(R!r[8][n]));
                        assert IsDivisibleBy(auts,(itM div st));
                        if [st*d:d in Divisors(auts)| st*d ge itm and st*d le itM] eq [itM] then
                            printf "proved! (%.3os)\n", Cputime()-t;
                            rec["inner_twists"] := [<1,a[2],a[3],a[4],a[5],a[6],a[7]>:a in rec["inner_twists"]];
                        else
                            printf "not proved (%.3os)\n", Cputime()-t;
                        end if;
                    end if;
                end if;
                */
            else
                if #InnerTwistTable gt 0 then
                    if IsDefined(InnerTwistTable,label) then
                        z := InnerTwistTable[label];  Ds := [1] cat rec["self_twist_discs"];
                        psis := [SplitCharacterOrbitLabel(s): s in StringToStrings(z[1])];  ms := atoii(z[2]);
                        for psi in psis do if not IsDefined(OT,psi[1]) then G,T := CharacterOrbitReps(psi[1]:RepTable);  OT[psi[1]] := <G,T>; end if; end for;
                        it := [<1,ms[i],psis[i][1],psis[i][2],Parity(psi),Order(psi),(d in Ds select d else 0) where d:=KroneckerDiscriminant(psi)>
                                   where psi:=OT[psis[i][1]][1][psis[i][2]] : i in [1..#psis]];
                        rec["inner_twists"] := [t:t in it|t[7] ne 0] cat [t:t in it|t[7] eq 0]; // put self twists first
                        rec["inner_twist_count"] := sum([t[2]:t in it]);
                        rec["has_non_self_twist"] := #psis gt #Ds select 1 else 0;
                        itproved := true;
                    else
                        printf "Warning: no record for newform %o found in InnerTwistTable\n", label;
                    end if;
                end if;
            end if;
            if #MinimalTwistTable gt 0 then
                if IsDefined(MinimalTwistTable,label) then
                    rec["minimal_twist"] := MinimalTwistTable[label];
                else
                    printf "Warning: no record for newform %o found in MinimalTwistTable\n", label;
                end if;
            end if;
            ro := IsDefined(RelatedObjects,label) select RelatedObjects[label] else [Parent("")|];
            if k gt 1 then
                rec["sato_tate_group"] := rec["is_cm"] eq 1 select Sprintf("%o.2.1.d%o",k-1,Order(chi)) else Sprintf("%o.2.3.c%o",k-1,Order(chi));
            end if;
            if k eq 2 and o eq 1 and dim eq 1 then Append(~ro, Sprintf("\"EllipticCurve/Q/%o/%o\"",N,Base26Encode(n-1))); end if;
            ero := [];
            if IsDefined(ArtinTable,label) then
                ar := ArtinTable[label];
                if #ar[6] gt 0 and ar[6] ne "?" then
                    L := atoii(ConreyTable[[r[1],r[3]]]);
                    arlabels := Split(ar[6],"c");
                    cn := StringToIntegerArray(arlabels[2]); assert #cn eq dim;
                    artin_url := "\"ArtinRepresentation/" cat arlabels[1] cat "\"";
                    Append(~ro,"\"ArtinRepresentation/" cat arlabels[1] cat "\"");  // Artin rep Galois orbit URL
                    if dim eq 1 then
                        artin_url := "\"ArtinRepresentation/" cat arlabels[1] cat "c1\"";
                        Append(~ero,[artin_url]);
                    else
                        // The artin rep labels of conjugates are in lex-order of an, we need to do the same for the cmfs
                        // When there is only one character in the character orbit this isn't necessary, but we do it as a sanity check anyway
                        assert n gt m and n le m+#r[10];
                        nn := n-m;
                        an := NFSeq(r[10][nn][1],r[10][nn][2],r[10][nn][5]);
                        xi := CharacterFromValues(N,r[17][n][1],[Parent(an[1])|z:z in r[17][n][2]]);
                        E := LabelEmbeddings(an,ConreyConjugates(chi,xi:ConreyIndexList:=L):Precision:=100);  assert #E eq dim;
                        rd := ExactQuotient(dim,Degree(chi));
                        ms := [(Index(L,e[1])-1)*rd + e[2]:e in E];
                        ccvcmp := func<v,w|&+[Abs(v[i]-w[i]):i in [1..#v]]>;
                        CC := ComplexField();
                        nbnd := 2;
                        while true do
                            tmp := [Conjugates(an[i]) : i in [1..nbnd]];  tmp := [[CC|tmp[i][j]:i in [1..nbnd]] : j in [1..dim]];
                            if Min([Min([ccvcmp(tmp[i],tmp[j]):j in [i+1..dim]]):i in [1..dim-1]]) gt 1 then break; end if;
                            nbnd *:= 2;
                        end while;
                        tmp := Sort([<ms[i],tmp[i]>:i in [1..dim]],func<a,b|CompareCCLists(a[2],b[2])>);  tmp :=[a[1]:a in tmp];
                        cn := [cn[Index(tmp,i)]:i in [1..dim]];
                        for i:=1 to dim do
                            artin_url := "\"ArtinRepresentation/" cat arlabels[1] cat "c" cat IntegerToString(cn[i]) cat "\"";
                            Append(~ero,[artin_url]);
                        end for;
                    end if;
                end if;
                D := eval(ar[7]);
                assert Set(D) eq Set(std);
                rec["projective_image_type"] := ar[8];
                rec["projective_image"] := ar[9];
                if #ar ge 10 and ar[10] ne "[]" then
                    f := eval(ar[10]);  assert #f gt 1;
                    rec["projective_field"] := f;
                    if IsDefined(FieldTable,f) then
                        rec["projective_field_label"] :=FieldTable[f];
                    else
                        if not f in unknown_fields then Include(~unknown_fields,f); PrintFile("unknown_fields.txt",sprint(f)); unknown_cnt +:= 1; end if;
                    end if;
                end if;
                if rec["minimal_twist"] ne "\\N" then assert rec["minimal_twist"] eq ar[11]; else rec["minimal_twist"] := ar[11]; end if;
                if #ar ge 12 and ar[12] ne "" and ar[12] ne "?" then rec["artin_degree"] := ar[12]; end if;
                if #ar ge 13 and ar[13] ne "" and ar[13] ne "?" then rec["artin_image"] := ar[13]; end if;
                if #ar ge 14 and ar[14] ne "" and ar[14] ne "?" and ar[14] ne "[]" then 
                    f:=eval(ar[14]);  assert #f gt 1;
                    rec["artin_field"] := f;
                    if IsDefined(FieldTable,f) then
                        rec["artin_field_label"] := FieldTable[f];
                    else
                        if not f in unknown_fields then Include(~unknown_fields,f); PrintFile("unknown_fields.txt",sprint(f)); unknown_cnt +:= 1; end if;
                    end if;
                end if;
                if #ar ge 15 then
                    rec["trace_zratio"] := ar[15];
                    rec["trace_moments"] := ar[16];
                    rec["trace_hash"] := ar[17];
                end if;
            end if;
            if rec["minimal_twist"] ne "\\N" then
                rec["is_twist_minimal"] := N eq StringToInteger(Split(rec["minimal_twist"],".")[1]) select 1 else 0;
            end if;
            rec["related_objects"] := ro;
            if #ero gt 0 then rec["embedded_related_objects"] := ero; end if;
            f := 0;
            if n le #r[8] then
                f := r[8][n];
                assert #f eq dim+1;
                rec["field_poly"] := f;
                rechnf["field_poly"] := f;
                if #f eq 2 then
                    // Do not mark field polynomial for Q as a cyclotomic or real cyclotomic polynomial (even if it is)
                    rec["field_disc"] := 1;
                    rec["field_disc_factorization"] := [];
                    rec["field_poly_is_cyclotomic"] := 0;
                    rec["field_poly_is_real_cyclotomic"] := 0;
                    rec["field_poly_root_of_unity"] := 0;
                    assert r[13][n] eq 1;
                    rec["is_polredabs"] := 1;
                    rec["nf_label"] := "1.1.1.1";
                else
                    zb,zn := IsCyclotomicPolynomial(R!f);
                    rec["field_poly_is_cyclotomic"] := zb select 1 else 0;
                    if zb then
                        rec["field_poly_is_real_cyclotomic"] := 0;
                    else
                        for m in EulerPhiInverse(2*dim) do if not IsDefined(RCP,m) then RCP[m]:=RealCyclotomicPolynomial(m); RCPI[RCP[m]]:=m; end if; end for;
                        zb := IsDefined(RCPI,R!f);
                        if zb then zn := RCPI[R!f]; end if;
                        rec["field_poly_is_real_cyclotomic"] := zb select 1 else 0;
                    end if;
                    rec["field_poly_root_of_unity"] := zb select zn else 0;
                    rec["is_polredabs"] := r[13][n];
                    if r[13][n] eq 1 then
                        if IsDefined(FieldTable,f) then
                            rec["nf_label"] := FieldTable[f];
                        else
                            if not f in unknown_fields then Include(~unknown_fields,f); PrintFile("unknown_fields.txt",sprint(f)); unknown_cnt +:= 1; end if;
                        end if;
                    end if;
                end if;
                if #r[14] ge n then rec["trace_zratio"] := Sprintf("%.3o",r[14][n]); end if;
                if #r[15] ge n then rec["trace_moments"] := [Sprintf("%.3o",m):m in r[15][n]]; end if;
                if #r[16] ge n then rec["trace_hash"] := r[16][n]; end if;
            end if;
            if #dims eq 1 then
                assert n eq 1 and (#r[9] eq 0 or #r[9][1] eq 0); rec["hecke_cutters"] := [];
            else
                if n le #r[9] then rec["hecke_cutters"] := r[9][n]; end if;
            end if;
            rec["is_self_dual"] := r[18][n];
            if n le m then
                if o gt 1 then rechnf["hecke_ring_character_values"] := [<r[17][n][1][i],r[17][n][2][i]>:i in [1..#r[17][n][1]]]; end if;
                rec["qexp_display"] := qExpansionStringOverQ(r[6][n],MIN_QEXP_DIGITS,MAX_QEXP_DIGITS);
                rec["hecke_ring_generator_nbound"] := 1;
                rec["hecke_ring_index"] := 1;
                rec["hecke_ring_index_factorization"] := [];
                rec["hecke_ring_index_proved"] := 1;
                rechnf["hecke_ring_cyclotomic_generator"] := 0;
                rechnf["hecke_ring_rank"] := 1;
                rechnf["hecke_ring_power_basis"] := 1;
                rechnf["an"] := sprint([[tr[i]]:i in [1..100]]);
                P := PrimesInInterval(1,#tr);
                rechnf["ap"] := sprint([[tr[p]] : p in P]);
                rechnf["maxp"] := P[#P];
                for p in LPP do Puts(lpoly_fp,Sprintf("%o:%o:%o",code,curly(sprint([1,-tr[p],(Integers()!chi(p))*p^(k-1)])),p)); end for; lpcnt +:= #LPP; Flush(lpoly_fp);
            end if;
            if n gt m and n le m+#r[10] then
                nn := n-m;
                assert f eq r[10][nn][1];
                assert #r[10][nn][2] eq dim;
                dens := [Integers()|LCM([Denominator(x):x in r[10][nn][2][i]]):i in [1..dim]];
                nums := [[Integers()|dens[i]*x:x in r[10][nn][2][i]]:i in [1..dim]];
                if r[10][nn][4][1] ne 0 then
                    assert (r[10][nn][4][1] lt 0 and r[18][n] eq 0 and IsEven(dim) and IsOdd(dim div 2)) or (r[10][nn][4][1] gt 0 and (r[18][n] eq 1 or IsDivisibleBy(dim,4)));
                    rec["field_disc"] := r[10][nn][4][1];
                    rec["field_disc_factorization"] := (r[10][nn][4][1] lt 0 select [<-1,1>] else []) cat r[10][nn][4][2];
                end if;
                rec["hecke_ring_generator_nbound"] := r[10][nn][7];
                rec["hecke_ring_index"] := r[10][nn][3];
                rec["hecke_ring_index_factorization"] := Factorization(r[10][nn][3]);
                rec["hecke_ring_index_proved"] := r[10][nn][4][1] eq 0 select 0 else 1;
                rechnf["hecke_ring_rank"] := dim;
                if k eq 1 and rec["field_poly_is_cyclotomic"] eq 1 then
                    rechnf["hecke_ring_power_basis"] := 0;
                    zzn := zn;
                    if IsOdd(zn) and IsEven(Order(chi)) then zzn := 2*zn; end if;
                    assert IsDivisibleBy(zzn,Order(chi));
                    a := NFSeq(r[10][nn][1],r[10][nn][2],r[10][nn][5]);
                    K := Universe(a);
                    zz := zn eq zzn select K.1 else -K.1;
                    rechnf["hecke_ring_cyclotomic_generator"] := zzn;
                    assert #r[17] ge n;
                    xi := CharacterFromValues(N,r[17][n][1],[K|x : x in r[17][n][2]]);
                    if o gt 1 then
                        u := r[10][nn][6][1];  v:= SparseZetaCharacterValues(xi,zz,zzn,u);
                        rechnf["hecke_ring_character_values"] := [<u[i],v[i]> : i in [1..#u]];
                    end if;
                    an := SparseZetaWeightOneCoefficients([a[p]:p in PrimesInInterval(1,100)],xi,zz,zzn);
                    assert #an eq 100;
                    rechnf["an"] := sprint(an);
                    P := PrimesInInterval(1,#a);
                    rechnf["ap"] := sprint(SparseZetaWeightOnePrimeCoefficients([a[p]:p in P],zz,zzn));
                    rechnf["maxp"] := P[#P];
                    // Convert to dense representation over [1,zeta_n,...,zeta_n^(n-1)] for call to qExpansionStringOverNF
                    function densify(a,n) v:=[0:i in [1..n]]; for t in a do v[t[2]+1]:=t[1]; end for; return v; end function;
                    rec["qexp_display"] := qExpansionStringOverNF([densify(z,zzn):z in an],MIN_QEXP_DIGITS,MAX_QEXP_DIGITS,zzn,0);
                    KR:=PolynomialRing(K);
                    for p in LPP do Puts(lpoly_fp,Sprintf("%o:%o:%o",code,curly(sprint(Eltseq(Norm(KR!1 - a[p]*KR.1 + xi(p)*p^(k-1)*KR.1^2)))),p)); end for;
                    lpcnt +:=#LPP; Flush(lpoly_fp);
                else
                    rechnf["hecke_ring_power_basis"] := (dens eq [1:i in [1..dim]] and nums eq [[i eq j select 1 else 0:i in [1..dim]]:j in [1..dim]]) select 1 else 0;
                    rechnf["hecke_ring_cyclotomic_generator"] := 0;
                    if rechnf["hecke_ring_power_basis"] eq 0 then
                        rechnf["hecke_ring_denominators"] := dens;
                        rechnf["hecke_ring_numerators"] := nums;
                        dd := dim;
                        A := (GL(dd,Rationals())!Matrix(r[10][nn][2]))^-1;
                        A := [[A[i][j]:j in [1..dd]]:i in [1..dd]];
                        idens := [LCM([Denominator(x):x in A[i]]):i in [1..#A]];
                        rechnf["hecke_ring_inverse_denominators"] := idens;
                        rechnf["hecke_ring_inverse_numerators"] := [[idens[i]*x:x in A[i]]:i in [1..#A]];
                    end if;
                    if o gt 1 then rechnf["hecke_ring_character_values"] := [<r[10][nn][6][1][i],r[10][nn][6][2][i]> : i in [1..#r[10][nn][6][1]]]; end if;
                    an := r[10][nn][5];
                    assert #an ge 100;
                    rechnf["an"] := sprint(an[1..100]);
                    P := PrimesInInterval(1,#an);
                    rechnf["ap"] := sprint([an[p] : p in P]);
                    rechnf["maxp"] := P[#P];
                    rec["qexp_display"] := qExpansionStringOverNF(r[10][nn][5],MIN_QEXP_DIGITS,MAX_QEXP_DIGITS,rec["field_poly_is_cyclotomic"] eq 1 select rec["field_poly_root_of_unity"] else 0,rechnf["hecke_ring_power_basis"]);
                    a := NFSeq(r[10][nn][1],r[10][nn][2],r[10][nn][5][1..Max(100,r[10][nn][7])]);
                    K := Universe(a);
                    xi := CharacterFromValues(N,r[17][n][1],[K|x : x in r[17][n][2]]);
                    KR:=PolynomialRing(K);
                    for p in LPP do Puts(lpoly_fp,Sprintf("%o:%o:%o",code,curly(sprint(Eltseq(Norm(KR!1 - a[p]*KR.1 + xi(p)*p^(k-1)*KR.1^2)))),p)); end for;
                    lpcnt +:=#LPP; Flush(lpoly_fp);
                end if;
            end if;
            s1 := Set([x:x in Keys(rec)]);  s2 := Set([t[1]: t in newforms_columns]);
            if s1 ne s2 then error Sprintf("newforms_columns match error diffs %o and %o", s1 diff s2, s2 diff s1); end if;
            str := bracket(Join([t[2] eq "text" select rec[t[1]] else (t[2][#t[2]] eq "]" select curly(bracket(s)) else s where s:=sprint(rec[t[1]])):t in newforms_columns],":"));
            Puts(newform_fp,str);  Flush(newform_fp);
            if rechnf["an"] ne "\\N" then
                hnfcnt +:= 1;
                s1 := Set([x:x in Keys(rechnf)]);  s2 := Set([t[1]: t in hecke_nf_columns]);
                if s1 ne s2 then error Sprintf("hecke_nf_columns match error diffs %o and %o", s1 diff s2, s2 diff s1); end if;
                str := bracket(Join([t[2] eq "text" select rechnf[t[1]] else (t[2][#t[2]] eq "]" select curly(bracket(s)) else s where s:=sprint(rechnf[t[1]])):t in hecke_nf_columns],":"));
                Puts(hecke_fp,str);  Flush(hecke_fp);
            end if;
            if Detail ge 0 then printf "%o (%.3os %oMB)\n",label,Cputime()-start, Memory(); end if;
            cnt +:= 1;
        end for;
    end for;
    printf "Wrote %o records to %o, and %o records to %o, and %o records to file %o, and %o records to file %o, total time %.3o secs\n", cnt, newform_outfile, hnfcnt, hecke_outfile, trcnt, trace_outfile, lpcnt, lpoly_outfile, Cputime()-start;
    if unknown_cnt gt 0 then printf "Appended %o unknown polredabs field polys to unknown_fields.txt\n", unknown_cnt; end if;
end procedure;

/*
....: for k in sorted(db.mf_nf_twists.col_type.keys()):
....:     if k != "id":
....:         print '<"%s","%s">,'%(k,db.mf_twists_nf.col_type[k])
....:     
*/
twists_nf_columns := [
<"conductor","integer">,
<"degree","integer">,
<"multiplicity","smallint">,
<"order","integer">,
<"parity","smallint">,
<"self_twist_disc","integer">,
<"source_char_orbit","smallint">,
<"source_dim","integer">,
<"source_hecke_orbit","integer">,
<"source_is_minimal","boolean">,
<"source_label","text">,
<"source_level","integer">,
<"target_char_orbit","smallint">,
<"target_dim","integer">,
<"target_hecke_orbit","integer">,
<"target_is_minimal","boolean">,
<"target_label","text">,
<"target_level","integer">,
<"twist_class_label","text">,
<"twist_class_level","integer">,
<"twisting_char_label","text">,
<"twisting_char_orbit","smallint">,
<"weight","smallint">
];

/*
    infile format is source:target:[psi1,...,psin],[m1,...mn]
    where source and target are newform labels, psi1,...psin are character orbit labels, and m1,...mn are multiplicities

    dimfile format is N:k:o:[d1,...,dn] where N=level, k=weight, o=charorbit, t=time (ignored), [d1...dn] is a list of dimension of newforms in newspace N.k.o
    (use mfsplit.txt for this)

    conreyfile format is  N:o:[n1,n2,...]:conductor:prim_index:order:deg:parity:isreal:isminimal (use conrey_XXX.txt)
*/
procedure FormatTwistDataNF (infile, outfile, conreyfile)
    start := Cputime();
    NewspaceDimsTable := AssociativeArray();
    S := Read("mfsplit.txt");  // format is N:k:o:[d1,...,dn]
    for s in Split(S) do r:=Split(s,":"); NewspaceDimsTable[[atoi(r[1]),atoi(r[2]),atoi(r[3])]] := atoii(r[4]); end for;
    printf "Loaded %o records from mfsplit.txt in %o secs.\n", #NewspaceDimsTable, Cputime()-start; start := Cputime();
    MinimalTwistTable := AssociativeArray();  MinimalTwistLevel := AssociativeArray();
    S := Read("mftwists_minimal.txt");  // format is source:target
    for s in Split(S) do r:=Split(s,":"); MinimalTwistTable[r[2]] := r[1]; MinimalTwistLevel[r[2]] := atoi(Split(r[1],".")[1]); end for;
    printf "Loaded %o records from mftwists_minimal.txt in %o secs.\n", #MinimalTwistTable, Cputime()-start; start := Cputime();
    T := [Split(r,":"):r in Split(Read(conreyfile),"\n")];
    CharacterTable:=IndexFibers(T,func<r|[atoi(r[1]),atoi(r[2])]>:Unique);
    printf "Loaded data for %o characters from file %o in %o secs.\n", #CharacterTable, conreyfile, Cputime()-start; start:=Cputime();
    S := [Split(r,":"):r in Split(Read(infile))];
    printf "Loaded %o records from %o in %.3os\n", #S, infile, Cputime()-start;  start := Cputime();
    function getchar(label)
        a := SplitCharacterOrbitLabel(label);
        r := CharacterTable[a][3]; n := atoi(Split(r[2..#r-1],",")[1]);
        return DirichletCharacter(a[1],n);
    end function;
    fp := Open(outfile,"w");
    write_header ("", fp, twists_nf_columns);
    rec := AssociativeArray(Parent(""));
    cnt := 0;
    for r in S do
        N,k,o,i := Explode(SplitNewformLabel(r[1]));
        rec["twist_class_label"] := MinimalTwistTable[r[1]];
        rec["twist_class_level"] := MinimalTwistLevel[r[1]];
        rec["source_label"] := r[1];
        rec["source_level"] := N;
        rec["source_char_orbit"] := o;
        rec["source_hecke_orbit"] := i;
        rec["source_is_minimal"] := N eq rec["twist_class_level"] and CharacterTable[[N,o]][10] eq "1" select "1" else "0";
        rec["source_dim"] := NewspaceDimsTable[[N,k,o]][i];
        rec["weight"] := k;
        N,k2,o,i := Explode(SplitNewformLabel(r[2]));
        assert k2 eq k;
        rec["target_label"] := r[2];
        rec["target_level"] := N;
        rec["target_char_orbit"] := o;
        rec["target_hecke_orbit"] := i;
        rec["target_is_minimal"] := N eq rec["twist_class_level"] and CharacterTable[[N,o]][10] eq "1" select "1" else "0";
        rec["target_dim"] := NewspaceDimsTable[[N,k,o]][i];
        chars := StringToStrings(r[3]);
        mults := atoii(r[4]);
        assert #chars gt 0 and #chars eq #mults;
        discs := atoii(r[5]);
        for i:=1 to #chars do
            rec["twisting_char_label"] := chars[i];
            c := CharacterTable[SplitCharacterOrbitLabel(chars[i])];
            assert c[1] eq c[4];
            rec["twisting_char_orbit"] := c[2];
            rec["multiplicity"] := mults[i];
            rec["conductor"] := c[4];
            rec["order"] := c[6];
            rec["degree"] := c[7];
            rec["parity"] := c[8];
            if c[6] eq "2" and rec["source_label"] eq rec["target_label"] then
                D := KroneckerDiscriminant(getchar(chars[i]));
                rec["self_twist_disc"] := D in discs select D else 0;
            else
                rec["self_twist_disc"] := c[6] eq "1" select 1 else 0;
            end if;
            s1 := Set([x:x in Keys(rec)]);  s2 := Set([t[1]: t in twists_nf_columns]);
            if s1 ne s2 then error Sprintf("twists_nf_columns match error diffs %o and %o", s1 diff s2, s2 diff s1); end if;
            Puts(fp,Join([sprint(rec[t[1]]):t in twists_nf_columns],":"));
            cnt +:= 1;
        end for;
        Flush(fp);
    end for;
    Flush(fp); delete fp;
    printf "Wrote %o records to %o, total time %.3o secs\n", cnt, outfile, Cputime()-start;
end procedure;

/*
sage: for k in sorted(db.mf_twists_cc.col_type.keys()):
....:     if k != "id":
....:         print '<"%s","%s">,'%(k,db.mf_twists_cc.col_type[k])
*/

twists_cc_columns := [
<"conductor","integer">,
<"degree","integer">,
<"order","integer">,
<"parity","smallint">,
<"source_conrey_index","integer">,
<"source_dim","integer">,
<"source_embedding_index","integer">,
<"source_hecke_orbit_code","bigint">,
<"source_is_minimal","boolean">,
<"source_label","text">,
<"source_level","integer">,
<"target_conrey_index","integer">,
<"target_dim","integer">,
<"target_embedding_index","integer">,
<"target_hecke_orbit_code","bigint">,
<"target_is_minimal","boolean">,
<"target_label","text">,
<"target_level","integer">,
<"twist_class_label","text">,
<"twist_class_level","integer">,
<"twisting_char_label","text">,
<"twisting_conrey_index","integer">,
<"weight","smallint">
];

/*
    infile format is source:target:[psi1,...,psin] where source and target are embedded newform labels N.k.a.x.n.i and psi1,...psin are Conrey labels q.n

    dimfile format is N:k:o:[d1,...,dn] where N=level, k=weight, o=charorbit, t=time (ignored), [d1...dn] is a list of dimension of newforms in newspace N.k.o
    (use mfsplit.txt for this)

    conreyfile format is  N:o:[n1,n2,...]:conductor:prim_index:order:deg:parity:isreal:isminimal (use conrey_XXX.txt)
*/
procedure FormatTwistDataCC (infile, outfile, conreyfile:Jobs:=1, JobId:=0)
    start := Cputime();
    NewspaceDimsTable := AssociativeArray();
    S := Read("mfsplit.txt");  // format is N:k:o:[d1,...,dn]
    for s in Split(S) do r:=Split(s,":"); NewspaceDimsTable[[atoi(r[1]),atoi(r[2]),atoi(r[3])]] := atoii(r[4]); end for;
    printf "Loaded %o records from mfsplit.txt in %o secs.\n", #NewspaceDimsTable, Cputime()-start; start := Cputime();
    MinimalTwistTable := AssociativeArray();  MinimalTwistLevel := AssociativeArray();
    S := Read("mftwists_cc_minimal.txt");  // format is source:target
    for s in Split(S) do r:=Split(s,":"); MinimalTwistTable[r[2]] := r[1]; MinimalTwistLevel[r[2]] := atoi(r[1][1..Index(r[1],".")-1]); end for;
    printf "Loaded %o records from mftwists_cc_minimal.txt in %o secs.\n", #MinimalTwistTable, Cputime()-start; start := Cputime();
    T := [Split(r,":"):r in Split(Read(conreyfile),"\n")];
    N := atoi(T[#T][1]);    // we assume conreyfile is sorted by level
    CharacterTable := [[0:i in [1..n]]:n in [1..N]];  cnt := 0;
    for i:=1 to #T do N := atoi(T[i][1]); ns := atoii(T[i][3]); for j in ns do CharacterTable[N][j] := i; cnt +:= 1; end for; end for;
    printf "Loaded data for %o characters in %o orbits from file %o in %o secs.\n", cnt, #T, conreyfile, Cputime()-start; start:=Cputime();
    S := [Split(r,":"):r in Split(Read(infile))];
    printf "Loaded %o records from %o in %.3os\n", #S, infile, Cputime()-start; start := Cputime();
    if Jobs gt 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    fp := Open(outfile,"w");
    if JobId eq 0 then write_header (Jobs gt 1 select "mf_twists_cc_header.txt" else "", fp, twists_cc_columns); end if;
    rec := AssociativeArray(Parent(""));
    cnt := 0;
    for r in S do
        N,k,o,i,n,j := Explode(SplitEmbeddedNewformLabel(r[1]));
        if N mod Jobs ne JobId then continue; end if;
        rec["twist_class_label"] := MinimalTwistTable[r[1]];
        rec["twist_class_level"] := MinimalTwistLevel[r[1]];
        rec["source_label"] := r[1];
        rec["source_level"] := N;
        rec["source_conrey_index"] := n;
        rec["source_embedding_index"] := j;
        rec["source_hecke_orbit_code"] := HeckeOrbitCode(N,k,o,i);
        rec["source_is_minimal"] := N eq rec["twist_class_level"] and T[CharacterTable[N][n]][10] eq "1" select "1" else "0";
        rec["source_dim"] := NewspaceDimsTable[[N,k,o]][i];
        rec["weight"] := k;
        N,k2,o,i,n,j := Explode(SplitEmbeddedNewformLabel(r[2]));
        assert k2 eq k;
        rec["target_label"] := r[2];
        rec["target_level"] := N;
        rec["target_conrey_index"] := n;
        rec["target_embedding_index"] := j;
        rec["target_hecke_orbit_code"] := HeckeOrbitCode(N,k,o,i);
        rec["target_is_minimal"] := N eq rec["twist_class_level"] and T[CharacterTable[N,n]][10] eq "1" select "1" else "0";
        rec["target_dim"] := NewspaceDimsTable[[N,k,o]][i];
        chars := StringToStrings(r[3]);
        for i:=1 to #chars do
            rec["twisting_char_label"] := chars[i];
            psi := SplitCharacterLabel(chars[i]);
            rec["twisting_conrey_index"] := psi[2];
            c := T[CharacterTable[psi[1]][psi[2]]];
            assert c[1] eq c[4] and atoi(c[4]) eq psi[1];
            rec["conductor"] := c[4];
            rec["order"] := c[6];
            rec["degree"] := c[7];
            rec["parity"] := c[8];
            s1 := Set([x:x in Keys(rec)]);  s2 := Set([t[1]: t in twists_cc_columns]);
            if s1 ne s2 then error Sprintf("twists_c_columns match error diffs %o and %o", s1 diff s2, s2 diff s1); end if;
            Puts(fp,Join([sprint(rec[t[1]]):t in twists_cc_columns],":"));
            cnt +:= 1;
        end for;
        Flush(fp);
    end for;
    Flush(fp); delete fp;
    printf "Wrote %o records to %o, total time %.3o secs\n", cnt, outfile, Cputime()-start;
end procedure;

/*
sage: for k in sorted(db.mf_twists_cc.col_type.keys()):
....:     if k != "id":
....:         print '<"%s","%s">,'%(k,db.mf_twists_cc.col_type[k])
*/
twists_cc_columns := [
<"conductor","integer">,
<"degree","integer">,
<"order","integer">,
<"parity","smallint">,
<"source_conrey_index","integer">,
<"source_dim","integer">,
<"source_hecke_orbit_code","bigint">,
<"source_label","text">,
<"source_level","integer">,
<"target_conrey_index","integer">,
<"target_dim","integer">,
<"target_hecke_orbit_code","bigint">,
<"target_label","text">,
<"target_level","integer">,
<"twist_class_label","text">,
<"twist_class_level","integer">,
<"twisting_char_label","text">,
<"twisting_conrey_index","integer">,
<"weight","smallint">
];


// Round real and imaginary parts of complex number z to accuracty of 1/absprec (so values within 1/(2*absprec) will come out the same)
function RoundCC(z,absprec)
    return Round(absprec*Real(z))/absprec + Round(absprec*Imaginary(z))/absprec * Parent(z).1;
end function;

function sprintreal(x,prec)
    if Abs(x) lt 10^10 and prec ge 20 and Abs(x-BestApproximation(x,1000)) lt 10^-(prec-1) then x := RealField(prec)!BestApproximation(x,1000); end if;
    s := Sprintf("%o",x);
    if "." in s and not "e" in s and not "E" in s then i:=#s; while s[i] eq "0" do i-:=1; end while; s := Substring(s,1,i); if s[#s] eq "." then Prune(~s); end if; if s eq "-0" then s:="0"; end if; end if;
    return s;
end function;
    
// Given ap, chi(p), p, and k, Satake parameters alpha_p are reciprocal roots of Lp(t/p^((k-1)/2))= 1 - ap/p^((k-1)/2)*t + chi(p)*t^2 (so Lp(t) = 1 - ap*t + chi(p)*p^(k-1)t^2)
// The Satake angles are theta_p = Arg(alpha_p)/(2*pi) in (-0.5,0.5], we take the smaller value.
function SatakeAngle(ap,chip,p,k,pi:nmax:=0)
    q := p^(k-1);
    // apply quadratic formula (inverted to take reciprocal root
    alpha1 := (2*chip) / (ap/Sqrt(q) + Sqrt(ap^2/q - 4*chip));
    alpha2 := (2*chip) / (ap/Sqrt(q) - Sqrt(ap^2/q - 4*chip));
    thetas := [Real(Arg(alpha1))/(2*pi),Real(Arg(alpha2))/(2*pi)];
    assert &and[theta ge -0.5 and theta le 0.5: theta in thetas];
    if k eq 1 then 
        if nmax eq 0 then nmax := 1000000; end if;
        rthetas := [BestApproximation(theta,nmax) : theta in thetas];
        assert &and[Abs(thetas[i]-rthetas[i]) lt 10^-10 : i in [1,2]];
        rthetas := [r eq -1/2 select 1/2 else r : r in rthetas];
        thetas := [Universe(thetas)!r : r in rthetas];
    else
        thetas := [t eq -0.5 select 0.5 else t : t in thetas];
    end if;
    return thetas[1] le thetas[2] select thetas[1] else thetas[2];
end function;

/*
sage: from lmfdb import db
sage: for k in sorted(db.mf_hecke_cc.col_type.keys()):
.,..:      print '<"%s","%s">,'%(k,db.mf_hecke_cc.col_type[k])
*/
hecke_cc_columns := [
<"an_normalized","double precision[]">,
<"angles","double precision[]">,
<"char_orbit_index","smallint">,
<"conrey_index","integer">,
<"dual_conrey_index","integer">,
<"dual_embedding_index","integer">,
<"dual_embedding_m","integer">,
<"embedding_index","integer">,
<"embedding_m","integer">,
<"embedding_root_imag","double precision">,
<"embedding_root_real","double precision">,
<"hecke_orbit","integer">,
<"hecke_orbit_code","bigint">,
<"label","text">,
<"level","integer">,
<"weight","smallint">
];

procedure FormatHeckeCCData (infile, outfile: Coeffs:=0, Precision:=20, DegreeBound:=0, Detail:=0, Jobs:=1, JobId:=0, conrey_labels:= "", ap_only:=false, SplitInput:=false)
    assert Jobs gt 0 and JobId ge 0 and JobId lt Jobs;
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    ConreyTable:=AssociativeArray();
    if conrey_labels ne "" then
        start:=Cputime();
        S := Split(Read(conrey_labels),"\n"); // format is N:o:[n1,n2,...] (list of conrey chars chi_N(n,*) in orbit o for modulus N)
        for s in S do r:=Split(s,":"); ConreyTable[[StringToInteger(r[1]),StringToInteger(r[2])]] := StringToIntegerArray(r[3]); end for;
        printf "Loaded %o records from conrey label file %o in %o secs.\n", #Keys(ConreyTable), conrey_labels, Cputime()-start;
    end if;
    start := Cputime();
    if SplitInput then infile cat:= Sprintf("_%o",JobId); end if;
    S := Split(Read(infile),"\n");
    printf "Loaded %o records from input file %o in %o secs.\n", #S, infile, Cputime()-start;
    start:=Cputime();
    outfp := Open(outfile,"w");
    if JobId eq 0 and not ap_only then write_header ("", outfp, hecke_cc_columns); end if;
    cnt := 0;
    prec := ap_only select Precision else 2*Precision+1; // make sure we use enough intermediate precision to compute Satake angles to target precision
    CC := ComplexField(prec);
    RR := RealField(prec);
    SetDefaultRealField(RR);    // Important!  We need the call to eval below to use the correct precision!
    pi := Pi(RR);
    coeffs := Coeffs gt 0 select Coeffs else 3000;
    T := AssociativeArray(Integers());
    Q := [[q[1]^q[2]:q in Factorization(n)]:n in [1..coeffs]];
    rec := AssociativeArray(Parent(""));
    for s in S do
        N := StringToInteger(Substring(s,1,Index(s,":")-1));
        if not SplitInput and ((N-JobId) mod Jobs) ne 0 then continue; end if;
        rs := Split(s,":");
        if rs[5] eq "[]" then continue; end if;
        r := <eval(a):a in rs>;
        N := r[1]; k := r[2]; o := r[3]; dims := r[5];
        rec["level"] := N;
        rec["weight"] := k;
        rec["char_orbit_index"] := o;
        if o gt 1 and not IsDefined(T,N) then T[N] := CharacterOrbitReps(N); end if;
        chi := o eq 1 select DirichletGroup(N)!1 else T[N][o];
        space_label := Sprintf("%o.%o.%o",N,k,Base26Encode(o-1));
        L := o eq 1 select [1] else ConreyTable[[r[1],r[3]]];
        off1 := #[d:d in dims|d eq 1];
        off2 := off1 + #r[10];
        assert #r[17] ge off2;
        // Dynamicall adjust coeffs if not specified
        if Coeffs eq 0 then if N le 1000 then coeffs := 1000; else if N le 4000 then coeffs := 2000; else coeffs:= 3000; end if; end if; end if;
        P := PrimesInInterval(1,coeffs);
        if not ap_only then Z := [(CC!n)^((k-1)/2):n in [1..coeffs]]; end if;   // precompute normalization factors here
        for i := 1 to #dims do
            if DegreeBound gt 0 and dims[i] gt DegreeBound then
                printf "Skipping form %o:%o:%o:%o because its dimension %o exceeds the specified degree bound %o.\n",N,k,o,i,dims[i],DegreeBound;
                break;
            end if;
            t := Cputime();
            newform_label := space_label cat "." cat Base26Encode(i-1);
            if i gt off2 and (#r lt 19 or i-off2 gt #r[19]) then
                printf "Warning: skipping form %o:%o:%o:%o because neither eignvalue nor embedding data is present.\n",N,k,o,i;
                break;
            end if;
            rec["hecke_orbit"] := i;
            rec["hecke_orbit_code"] := HeckeOrbitCode(N,k,o,i);
            d := dims[i];
            cd := Degree(chi); rd := ExactQuotient(d,cd);
            if i le off2 then
                // Here if we have exact eigenvalue data (including dimension 1 case where eigenvalues are integers)
                if i gt off1 then X := r[10][i-off1]; a := NFSeq(X[1],X[2],X[5]); K := Parent(a[1]); else a := r[6][i]; K := Rationals(); end if;
                assert #a ge coeffs;
                assert d eq Degree(K);
                xi := CharacterFromValues(N,r[17][i][1],[K|z:z in r[17][i][2]]);
                // use more precision here, we need to be sure to separate conjugates
                E := d gt 1 select LabelEmbeddings(a,ConreyConjugates(chi,xi:ConreyIndexList:=L):Precision:=Max(prec,100)) else [[L[1],1]];
                root := d gt 1 select Conjugates(Parent(a[1]).1:Precision:=prec) else [CC!0];
                if ap_only then
                    A :=  [Conjugates(a[p]:Precision:=prec) : p in P];
                else
                    A := [Conjugates(a[n]:Precision:=prec) : n in [1..coeffs]];
                    C := [Conjugates(xi(p):Precision:=prec) : p in P];
                end if;
                Edual := E;
                if r[18][i] ne 1 then
                    // if not self-dual then K is totally complex and Magma always lists embeddings as conjugate pairs 
                    assert IsEven(d);
                    for j in [1..(d div 2)] do Edual[2*j-1] := E[2*j]; Edual[2*j] := E[2*j-1]; end for;
                end if;
            else
                // Here if we are working with embedded eigenvalue data, in which case we assume that the embeddings are given to us in the correct order
                // i.e. grouped by Conrey index (ordered by index) and lex-ordered an-lists [[re,im],...] for embeddings with the same character embedding
                assert #r[19][i-off2] eq d and &and[#r[19][i-off2][n] ge #P : n in [1..d]];
                E := &cat[[[m,n]:n in [1..rd]]:m in L];
                // in this case we assume we don't have defining polynomial for the coefficient field and do not try to match roots to embeddings
                root := [];
                // sanity check to make sure we haven't been asked for more precision than we have available -- this is a total hack, we just count digits in the
                // decimal representation of the first a_2 in the list, but it will catch some obvious mistakes.  We really should store the precision in the mfdata file.
                assert Index(rs[19],",") ge prec+4;
                assert #r[19][i-off2][1] ge #P;
                cchi := [ComplexConreyCharacter(N,j,CC):j in L];
                cchi := &cat[[cchi[j]:i in [1..rd]]:j in [1..cd]];
                A := [[CC|a : a in anlist_from_aplist(N,k,cchi[m],[CC!r[19][i-off2][m][j]:j in [1..#P]],coeffs:FactorTable:=Q)] : m in [1..d]];
                if o eq 1 then 
                    // For backward compatibility, when chi is trivial we do not assume the embeddings are sorted and sort them if necessary
                    if not &and[Real(A[i][2]) lt Real(A[i+1][2]):i in [1..#A-1]] then A := Sort(A,CompareCCLists); end if;
                end if;
                if ap_only then
                    A := [[CC|A[m][p]:m in [1..d]] : p in P];  // transpose to match NF conjugates (consistent with exact eigenvalue case)
                else
                    A := [[CC|A[m][n]:m in [1..d]] : n in [1..coeffs]];                 // transpose to match NF conjugates (as above)
                    C := [[cchi[m](p):m in [1..d]]: p in P];
                end if;
                Edual := E;
                if r[18][i] ne 1 then
                    assert IsEven(d);
                    B := 16;
                    while B le coeffs do
                        X := [Round(100*&+[n*Real(A[n][m]/Z[n])^3:n in [1..B]]):m in [1..d]];
                        if 2*#Set(X) eq d and &and[Multiplicity(Multiset(X),x) eq 2 : x in Set(X)] then break; end if;
                        B *:= 2;  if B gt coeffs and B lt 2*coeffs then B := coeffs; end if;
                    end while;
                    if B gt coeffs then
                        printf "Warning: unable to identify conjugatee embeddings for form %o, dual-embedding data will be omitted\n", newform_label;
                        print Multiset(X);
                        Edual := [];
                    else
                        X := Sort([[X[j],j]:j in [1..#X]]);
                        for j:= 1 to d div 2 do Edual[X[2*j-1][2]] := E[X[2*j][2]]; Edual[X[2*j][2]] := E[X[2*j-1][2]]; end for;
                    end if;
                end if;
            end if;
            if k eq 1 then nmax := Max(EulerPhiInverse(2*d)); else nmax := 0; end if;
            for m := 1 to d do
                e := E[m];
                rec["label"] := Sprintf("%o.%o.%o",newform_label,e[1],e[2]);
                rec["conrey_index"] := e[1];
                rec["embedding_index"] := e[2];
                rec["embedding_m"] := (Index(L,e[1])-1)*rd + e[2];
                if #Edual eq 0 then
                    rec["dual_conrey_index"] := "\\N"; rec["dual_embedding_index"] := "\\N"; rec["dual_embedding_m"] := "\\N";
                else
                    edual := Edual[m];
                    rec["dual_conrey_index"] := edual[1];
                    rec["dual_embedding_index"] := edual[2];
                    rec["dual_embedding_m"] := (Index(L,edual[1])-1)*rd + edual[2];
                end if;
                rec["embedding_root_real"] := #root gt 0 select sprintreal(Real(root[m]),Precision) else "\\N";
                rec["embedding_root_imag"] := #root gt 0 select sprintreal(Imaginary(root[m]),Precision) else "\\N";
                if ap_only then
                    // don't normalize or use curly braces here, this data is being used to compute L-functions and is not to be loaded directly into postgres
                    ap := sprint([[sprintreal(Real(A[n][m]),Precision),sprintreal(Imaginary(A[n][m]),Precision)] : n in [1..#P]]);
                    str := bracket(strip(Sprintf("%o:%o:%o:%o:%o:%o",rec["hecke_code,"],rec["label"],e[1],e[2],rec["embedding_m"],ap)));
                else
                    // normalize an here
                    rec["an_normalized"] := curly(sprint([[sprintreal(Real(A[n][m]/Z[n]),Precision),sprintreal(Imaginary(A[n][m]/n^((k-1)/2)),Precision)] : n in [1..coeffs]]));
                    rec["angles"] := curly(sprint([(GCD(N,p) eq 1 select sprintreal(SatakeAngle(A[p][m],C[j][m],p,k,pi:nmax:=nmax),Precision) else "null") where p:=P[j] : j in [1..#P]]));
                    s1 := Set([x:x in Keys(rec)]);  s2 := Set([t[1]: t in hecke_cc_columns]);
                    if s1 ne s2 then error Sprintf("hecke_cc_columns match error diffs %o and %o", s1 diff s2, s2 diff s1); end if;
                    str := bracket(Join([sprint(rec[t[1]]):t in hecke_cc_columns],":"));
                    // strip(Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o",code,lfunc_label,e[1],e[2],embedding_m,reroot,imroot,an,angles)));
                end if;
                if Detail gt 0 then print str; end if;
                Puts(outfp,str);  cnt +:= 1;
                Flush(outfp);
            end for;
            if Detail ge 0 then printf "Computed CC eignenvalue data (%o coeffs, %o digits) for form %o:%o:%o:%o(%o) of dimension %o in %os (%os)\n",coeffs,Precision,N,k,o,i,newform_label,d,Cputime()-t,Cputime()-start; end if;
        end for;
        Flush(outfp);
    end for;
    printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start;
end procedure;
            
procedure CreateSubspaceData (outfile, dimfile, conrey_labels: MaxN:=0, Detail:=0, Jobs:=1, JobId:=0)
    assert Jobs gt 0 and JobId ge 0 and JobId lt Jobs;
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    start:=Cputime();
    S := [Split(r,":"): r in Split(Read(dimfile),"\n")];
    S := [[StringToInteger(a):a in r]:r in S];
    DT := AssociativeArray();
    B := 0; B1:= 0; b := 1;
    for r in S do DT[[r[1],r[2],r[3]]]:=[r[4],r[6]]; B := Max(B,r[1]*r[2]*r[2]); if r[2] eq 1 then B1:=Max(B1,r[1]); end if; if r[3] gt 1 then b := 0; end if; end for;
    printf "Loaded %o records from dimension file %o in %os, set B to %o and B1 to %o and b to %o (%o)\n", #S, dimfile, Cputime()-start, B, B1, b, b eq 0 select "all chars" else "triv char only";
    delete S;
    CT:=AssociativeArray();  PT := AssociativeArray();
    start:=Cputime();
    S := Split(Read(conrey_labels),"\n"); // format is N:o:[n1,n2,...]:M:po:ord:deg:parity:isreal (list of conrey chars chi_N(n,*) in orbit o, M=cond, po=primi_orbit_index
    for s in S do
        r:=Split(s,":");
        N := StringToInteger(r[1]); i := StringToInteger(r[2]); clabels := StringToIntegerArray(r[3]); M := StringToInteger(r[4]); h := StringToInteger(r[5]);
        CT[[N,i]] := <clabels,M,h>;
        PT[[M,h,N]] := i;
    end for;
    printf "Loaded %o records from conrey label file %o in %o secs.\n", #Keys(CT), conrey_labels, Cputime()-start;
    start:=Cputime();
    outfp := Open(outfile,"w");
    if JobId eq 0 then
        headfp := Jobs gt 1 select Open("mf_subspaces_header.txt","w") else outfp;
        Puts(headfp,"label:level:weight:char_orbit_index:char_orbit_label:conrey_indexes:sub_label:sub_level:sub_char_orbit_index:sub_char_orbit_label:sub_conrey_indexes:sub_dim:sub_mult");
        Puts(headfp,"text:integer:smallint:smallint:text:integer[]:text:integer:smallint:text:integer[]:integer:integer");
        Puts(headfp,"");
        Flush(headfp);
    end if;
    NewDimTable := AssociativeArray();
    id := 0;
    if MaxN eq 0 then MaxN := B; end if;
    for N:=1 to MaxN do
        if b eq 1 and Floor(Sqrt(B/N)) lt 2 then break; end if;
        if ((N-JobId) mod Jobs) ne 0 then continue; end if;
        t := Cputime();
        for i:=1 to NumberOfCharacterOrbits(N) do
            i_label := Base26Encode(i-1);
            r := CT[[N,i]];
            C := r[2];  h := r[3];
            subs := [*<M,PT[[C,h,M]],#Divisors(ExactQuotient(N,M))> where M := C*D : D in Divisors(ExactQuotient(N,C))*];
            for k in [(N le B1 select 1 else 2)..Floor(Sqrt(B/N))] do
                dim := DT[[N,k,i]][1];  newdim := DT[[N,k,i]][2];
                dims := [DT[[sub[1],k,sub[2]]][2] : sub in subs];
                mults := [sub[3]: sub in subs];
                assert &+[dims[n]*mults[n]: n in [1..#subs]] eq dim;
                label := NewspaceLabel(N,k,i);
                for n:=1 to #subs do
                    if dims[n] eq 0 then continue; end if;
                    id +:= 1;
                    M := subs[n][1];
                    j := subs[n][2];
                    j_label := Base26Encode(j-1);
                    sub_label := NewspaceLabel(M,k,j);
                    str := strip(Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o",
                            label,N,k,i,i_label,curly(sprint(i gt 1 select r[1] else [1])),sub_label,M,j,j_label,curly(sprint(j gt 1 select CT[[M,j]][1] else [1])),dims[n],mults[n]));
                    if Detail gt 0 then print str; end if;
                    Puts(outfp,str);
                    Flush(outfp);
                end for;
            end for;
        end for;
        printf "Time to complete level %o was %os (%os)\n", N,Cputime()-t,Cputime()-start;
        Flush(outfp);
    end for;
    printf "Wrote %o records to %o in %o secs\n", id, outfile, Cputime()-start;
end procedure;
                
procedure CreateGamma1SubspaceData (outfile, dimfile: Detail:=0, SkipWeightOne:=false, MaxN:=0, MaxNk2:=0)
    start := Cputime();
    DT := AssociativeArray();
    if #dimfile gt 0 then
        M := 0; Mk2 := 0;
        S := [Split(r,":"): r in Split(Read(dimfile),"\n")];
        S := [[StringToInteger(a):a in r]:r in S];
        for r in S do DT[[r[1],r[2],r[3]]]:=[r[4],r[6]]; M := Max(M,r[1]); Mk2 := Max(Mk2,r[1]*r[2]*r[2]); end for;
        printf "Loaded %o records from dimension file %o in %os\n", #S, dimfile, Cputime()-start;
        if MaxN eq 0 then MaxN := M; end if;
        if MaxNk2 eq 0 then MaxNk2 := Mk2; end if;
    else
        assert SkipWeightOne and MaxNk2 gt 0;
    end if;
    if MaxN eq 0 then MaxN := SkipWeightOne select (MaxNk2 div 4) else MaxNk2; end if;
    printf "Creating Gamma1 subspace table for N <= %o and Nk2 <= %o%o\n", MaxN, MaxNk2, SkipWeightOne select " (and k > 1)" else "";
    start := Cputime();
    fp := Open(outfile,"w");
    Puts(fp,"label:level:weight:sub_level:sub_dim:sub_mult");
    Puts(fp,"text:integer:smallint:integer:integer:integer");
    Puts(fp,"");
    // Computing dimensions of cuspidal and new cuspidal subspaces of Gamma1 is quick so we do it on the fly
    T := AssociativeArray();
    cnt := 0;
    for N in [1..MaxN] do
        oN := NumberOfCharacterOrbits(N);
        t := Cputime();
        subs := [<M,#Divisors(ExactQuotient(N,M))> : M in Divisors(N)];
        for k in [(SkipWeightOne select 2 else 1)..Floor(Sqrt(MaxNk2/N))] do
            if #DT ne 0 then
                dim := &+[DT[[N,k,i]][1]:i in [1..oN]];
                newdim := &+[DT[[N,k,i]][2]:i in [1..oN]];
                if k gt 1 then assert dim eq DimensionCuspFormsGamma1(N,k) and newdim eq DimensionNewCuspFormsGamma1(N,k); end if;
            else
                dim := DimensionCuspFormsGamma1(N,k);
                newdim := DimensionNewCuspFormsGamma1(N,k);
            end if;
            assert dim - newdim eq sum([T[[sub[1],k]]*sub[2] : sub in subs | sub[1] ne N]);
            T[[N,k]] := newdim;
            dims := [T[[sub[1],k]] : sub in subs];
            mults := [sub[2]: sub in subs];
            assert &+[dims[n]*mults[n]: n in [1..#subs]] eq dim;
            for n:=1 to #subs do
                if dims[n] eq 0 then continue; end if;
                cnt +:= 1;
                str := strip(Sprintf("%o.%o:%o:%o:%o:%o:%o", N,k,N,k,subs[n][1],dims[n],mults[n]));
                if Detail gt 0 then print str; end if;
                Puts(fp,str);
            end for;
        end for;
        printf "Time to complete Gamma1 level %o was %os (%os)\n", N,Cputime()-t,Cputime()-start;
        Flush(fp);
    end for;
    printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start;
end procedure;

// infile should have records formatted as N:k:o:D:... where D is a vector of dimensions of newforms, only needed for k=1, but will verify other dimensions
// output format is N:k:o:dS:dE:dNS:dNE
procedure CreateDimensionTable(infile,outfile:MaxN:=0,MaxNk2:=0,TrivialCharOnly:=false,Detail:=0,Jobs:=1,JobId:=0)
    assert Jobs gt 0 and JobId ge 0 and JobId lt Jobs;
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    start := Cputime();
    if #infile gt 0 then S := Split(Read(infile),"\n"); else S:=[]; end if;
    A := AssociativeArray();
    M := 0;  Mk2 := 0;
    for s in S do
        r := Split(s,":");
        N := StringToInteger(r[1]);  k := StringToInteger(r[2]);  o:= StringToInteger(r[3]); D := eval(r[4]);
        if TrivialCharOnly and o gt 1 then continue; end if;
        A[[N,k,o]]:= sum(D);
        if N gt M then M := N; end if;
        if N*k*k gt Mk2 then Mk2 := N*k*k; end if;
    end for;
    if MaxN eq 0 then MaxN := M; end if;
    if MaxNk2 eq 0 then MaxNk2 := Mk2; end if;
    printf "Loaded %o records from input file %o in %os\n", #S, infile, Cputime()-start;
    delete S;
    O := AssociativeArray();
    fp := Open(outfile,"w");
    b := TrivialCharOnly select 1 else 0;
    printf "Creating dimension table for N <= %o and Nk2 <= %o%o\n", MaxN, MaxNk2, TrivialCharOnly select " (trivial char only)" else "";
    for N:=1 to MaxN do
        if ((N-JobId) mod Jobs) ne 0 then continue; end if;
        n := 0; start := Cputime();
        G,T := CharacterOrbitReps(N:RepTable,OrderBound:=b);
        O[N] := T;
        for o:=1 to #G do
            // Don't waste time on trivial character once level rules out everything but weight 1
            if o eq 1 and Floor(Sqrt(MaxNk2/N)) le 1 then Puts(fp,Sprintf("%o:1:1:0:0:0:0",N)); n +:= 1; continue; end if;
            chi := G[o];
            psi := AssociatedPrimitiveCharacter(chi);
            C := Modulus(psi);
            subN := [C*D:D in Divisors(ExactQuotient(N,C))];
            for M in subN do if not IsDefined(O,M) then O[M] := T where _,T:=CharacterOrbitReps(M:RepTable,OrderBound:=b); end if; end for;
            subs := [*<M,O[M][FullDirichletGroup(M)!psi],#Divisors(ExactQuotient(N,M))> : M in subN *];
            for k:=1 to Floor(Sqrt(MaxNk2/N)) do
                if k gt 1 then
                    dS := QDimensionCuspForms(chi,k);
                    dNS := QDimensionNewCuspForms(chi,k);
                end if;
                dE := QDimensionEisensteinForms(chi,k);
                dNE := QDimensionNewEisensteinForms(chi,k);
                if IsDefined(A,[N,k,o]) then
                    dStab := &+[s[3]*A[[s[1],k,s[2]]] : s in subs];
                    dNStab := A[[N,k,o]];
                    if k gt 1 then assert dStab eq dS and dNStab eq dNS; else dS := dStab; dNS := dNStab;
                    end if;
                else
                    if k eq 1 then printf "Missing required dimension data for space %o:%o:%o!\n",N,k,o; assert k ne 1; end if;
                end if;
                n +:= 1;
                str := strip(Sprintf("%o:%o:%o:%o:%o:%o:%o",N,k,o,dS,dE,dNS,dNE));
                if Detail gt 0 then print str; end if;
                Puts(fp,str);
            end for;
        end for;
        Flush(fp);
        printf "Wrote %o records for level %o in %os\n", n, N, Cputime()-start;
    end for;
end procedure;

// infile should have records formatted as N:k:i
// output format is N:k:o:dS:dE:dNS:dNE
procedure CreateDimensionTableTwo(outfile,MaxNk2:MaxN:=0,Jobs:=1,JobId:=0)
    assert Jobs gt 0 and JobId ge 0 and JobId lt Jobs;
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    start := Cputime();
    fp := Open(outfile,"w");
    if MaxN eq 0 then MaxN := Floor(MaxNk2/4); end if;
    for N:=1 to MaxN do
        if ((N-JobId) mod Jobs) ne 0 then continue; end if;
        n := 0; start := Cputime();
        G := CharacterOrbitReps(N);
        for o:=1 to #G do
            chi := G[o];
            for k:=2 to Floor(Sqrt(MaxNk2/N)) do
                dS := QDimensionCuspForms(chi,k);
                dNS := QDimensionNewCuspForms(chi,k);
                dE := QDimensionEisensteinForms(chi,k);
                dNE := QDimensionNewEisensteinForms(chi,k);
                n +:= 1;
                str := strip(Sprintf("%o:%o:%o:%o:%o:%o:%o",N,k,o,dS,dE,dNS,dNE));
                Puts(fp,str);
            end for;
        end for;
        Flush(fp);
        printf "Wrote %o records for level %o in %os\n", n, N, Cputime()-start;
    end for;
end procedure;

/*
sage: from lmfdb import db
sage: for k in sorted(db.char_dir_orbits.col_type.keys()):
         print '<"%s","%s">,'%(k,db.char_dir_orbits.col_type[k])
*/
char_dir_orbits_columns := [
<"char_degree","integer">,
<"conductor","integer">,
<"galois_orbit","integer[]">,
<"is_minimal","boolean">,
<"is_primitive","boolean">,
<"is_real","boolean">,
<"label","text">,
<"modulus","integer">,
<"orbit_index","smallint">,
<"orbit_label","text">,
<"order","integer">,
<"parity","smallint">,
<"prim_orbit_index","integer">
];

/*
    infile format is N:o:[n1,n2,...]:conductor:prim_index:order:deg:parity:isreal:isminimal (use conrey_XXX.txt)
*/
procedure FormatCharacterOrbitTable(infile,outfile)
    start := Cputime();
    S := getrecs(infile);
    printf "Loaded %o records from %o in %.3o secs\n", #S, infile, Cputime()-start;
    fp := Open(outfile,"w");
    write_header ("", fp, char_dir_orbits_columns);
    rec := AssociativeArray();
    cnt := 0;
    for r in S do
        rec["modulus"] := r[1];
        rec["orbit_index"] := r[2];
        rec["label"] := r[1] cat "." cat Base26Encode(atoi(r[2])-1);
        rec["orbit_label"] := r[1] cat "." cat r[2];
        rec["galois_orbit"] := curly(r[3]);
        rec["conductor"] := r[4];
        rec["prim_orbit_index"] := r[5];
        rec["is_primitive"] := r[1] eq r[4] select "t" else "f";  if rec["is_primitive"] eq "t" then assert r[2] eq r[5]; end if;
        rec["order"] := r[6];
        rec["char_degree"] := r[7];
        rec["parity"] := r[8];
        rec["is_real"] := r[9] eq "1" select "t" else "f";
        rec["is_minimal"] := r[10] eq "1" select "t" else "f";
        s1 := Set([x:x in Keys(rec)]);  s2 := Set([t[1]: t in char_dir_orbits_columns]);
        if s1 ne s2 then error Sprintf("twists_columns match error diffs %o and %o", s1 diff s2, s2 diff s1); end if;
        Puts(fp,Join([sprint(rec[t[1]]):t in char_dir_orbits_columns],":"));
        cnt +:= 1;
    end for;
    Flush(fp); delete fp;
    printf "Wrote %o records to %o, total time %.3o secs\n", cnt, outfile, Cputime()-start;
end procedure;

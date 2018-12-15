Attach("chars.m");
Attach("mfdims.m");
Attach("mfchars.m");
load "mf.m"; // needed to reconstruct form from Hecke cutters

// TODO: add null hecke cutter in weight 1

// empty sum is 0, empty product is 1
function sum(X) return #X eq 0 select 0 else &+X; end function;
function prod(X) return #X eq 0 select 1 else &*X; end function;

// strip is shockingly slow so we roll our own (we are only concerned with spaces and line breaks)
function strip(X) return Join(Split(Join(Split(X," "),""),"\n"),""); end function;

function SturmBound (N, k)
    m := Index(Gamma0(N));
    return Integers()!Floor(m*k/12-(m-1)/N);
end function;

function NewformSturmBound (N, k, chi)
    m := Index(Gamma0(N));
    M := ExactQuotient(N,Conductor(chi));
    n := #[p:p in PrimeDivisors(N)|not IsDivisibleBy(M,p)];
    return Integers()!Floor(m*k/(2^n*12));
end function;

function AnalyticConductor (N, k)
    return N*(2*Exp(Psi((1+k)/2)))^2;
end function;

alphabet := "abcdefghijklmnopqrstuvwxyz";

function Base26Encode(n)
    s := alphabet[1 + n mod 26]; n := ExactQuotient(n-(n mod 26),26);
    while n gt 0 do
        s := alphabet[1 + n mod 26] cat s; n := ExactQuotient(n-(n mod 26),26);
    end while;
    return s;
end function;

// encode Hecke orbit as a 64-bit integer
function HeckeOrbitCode (N,k,i,n)
    return N+2^24*k+2^36*(i-1)+2^52*(n-1);
end function;

// extract Hecke orbit invariants from code
function SplitHeckeOrbitCode(c)
    N := c mod 2^24;  c := ExactQuotient(c-N,2^24);
    k := c mod 2^12;  c := ExactQuotient(c-k,2^12);
    i := (c mod 2^16)+1; c := ExactQuotient(c-(i-1),2^16);
    n := c+1;
    return N,k,i,n;
end function;

function NewspaceLabel(N,k,i)
    return Sprintf("%o.%o.%o",N,k,Base26Encode(i-1));
end function;

function NewformLabel(N,k,i,n)
    return NewspaceLabel(N,k,i) cat "." cat Base26Encode(n-1);
end function;

// return latex string for cv^e, where c is an integer, v is a string (e.g. "q" or "\beta"), and e is a positive integer
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

function LatexSubTerm(c,v,e:First:=false,SubscriptZeroIsOne:=false)
    if c eq 0 then return ""; end if;
    if SubscriptZeroIsOne and e eq 0 then
        if c eq 1 then return (First select "1" else "+1"); end if;
        if c eq -1 then return "-1"; end if;
        v:=""; es:="";
    else
        es := Sprintf("_{%o}",e);
    end if;
    if c eq 1 then return (First select "" else "+") cat v cat es; end if;
    if c eq -1 then return "-" cat v cat es; end if;
    if Abs(c) gt 10 then b,p,n := IsPower(Abs(c)); else b := false; end if;
    s := Sign(c) eq 1 select (First select "" else "+") else "-";
    s cat:= b select Sprintf("%o^{%o}",p,n) cat v else IntegerToString(Abs(c)) cat v;
    return s cat es;
end function;

function qExpansionStringOverNF(a,prec)
    d := #a[1];
    zero := [0: i in [1..d]];
    one := [1] cat [0:i in [2..d]];
    assert d gt 1 and a[1] eq one;
    s := "q";
    // find first nonzero coeff
    n := 2;  digits := 0;
    while n le #a and ((digits eq 0) or digits lt prec) do
        if a[n] ne zero then
            if &and[a[n][i] eq 0 : i in [2..#a[n]]] then
                s cat:= LatexTerm(a[n][1],"q",n);
                digits +:= 1;
             else
                if #[c:c in a[n]|c ne 0] eq 1 then
                    i:=[j:j in [1..#a[n]]|a[n][j] ne 0][1];
                    s cat:= LatexSubTerm(a[n][i],"\\\\beta",i-1:SubscriptZeroIsOne);
                else
                    s cat:= "+(";
                    i := 1;
                    while i le #a[n] and digits lt prec do
                        if a[n][i] ne 0 then
                            s cat:= LatexSubTerm(a[n][i],"\\\\beta",i-1:First:=(s[#s] eq "("),SubscriptZeroIsOne);
                            digits +:= 1;
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
    return s cat "+\\\\cdots";
end function;

function qExpansionStringOverQ(a,prec)
    assert a[1] eq 1;
    s := "q";
    n := 2;  digits := 0;
    while digits lt prec and n le #a do
        s cat:= LatexTerm(a[n],"q",n);
        digits +:= a[n] eq 0 select 0 else 1;
        n +:= 1;
    end while;
    return s cat "+\\\\cdots";
end function;

procedure FormatNewspaceData (infile, outfile, conrey_labels, dimfile: Detail:=0, Jobs:=1, JobId:=0)
    assert Jobs gt 0 and JobId ge 0 and JobId lt Jobs;
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    start:=Cputime();
    S := Split(Read(conrey_labels),"\n"); // format is N:o:[n1,n2,...] (list of conrey chars chi_N(n,*) in orbit o for modulus N)
    ConreyTable:=AssociativeArray();
    for s in S do r:=Split(s,":"); ConreyTable[[StringToInteger(r[1]),StringToInteger(r[2])]] := r[3]; end for;
    printf "Loaded %o records from conrey label file %o in %o secs.\n", #Keys(ConreyTable), conrey_labels, Cputime()-start;
    start:=Cputime();
    S := [Split(r,":"): r in Split(Read(dimfile),"\n")];
    S := [[StringToInteger(a):a in r]:r in S];
    DT := AssociativeArray();
    for r in S do DT[[r[1],r[2],r[3]]]:=[r[4],r[5],r[6],r[7]]; end for;
    printf "Loaded %o records from dimension file %o in %os\n", #S, dimfile, Cputime()-start;
    start := Cputime();
    S := Split(Read(infile),"\n");
    printf "Loaded %o records from input file %o in %os\n", #S, infile, Cputime()-start;
    start := Cputime();
    outfp := Open(outfile,"w");
    if JobId eq 0 then
        headfp := Jobs gt 1 select Open("mf_newspaces_header.txt","w") else outfp;
        Puts(headfp,"label:level:level_radical:level_primes:weight:odd_weight:analytic_conductor:Nk2:char_orbit_index:char_orbit_label:char_labels:char_order:char_conductor:prim_orbit_index:char_degree:char_parity:char_is_real:char_values:sturm_bound:trace_bound:dim:num_forms:hecke_orbit_dims:eis_dim:eis_new_dim:cusp_dim:mf_dim:mf_new_dim:AL_dims:plus_dim");
        Puts(headfp,"text:integer:integer:jsonb:smallint:boolean:double precision:integer:integer:text:jsonb:integer:integer:integer:integer:smallint:boolean:jsonb:integer:integer:integer:smallint:jsonb:integer:integer:integer:integer:integer:jsonb:integer");
        Puts(headfp,"");
        Flush(headfp); delete(headfp);
    end if;
    OT := AssociativeArray();
    cnt := 0;
    for s in S do
        N := StringToInteger(Substring(s,1,Index(s,":")-1));
        if ((N-JobId) mod Jobs) ne 0 then continue; end if;
        r := Split(s,":");
        k := StringToInteger(r[2]); o := StringToInteger(r[3]); dims := eval(r[5]); traces := eval(r[6]);
        analytic_conductor := AnalyticConductor(N,k);
        num := #dims;
        assert #traces eq num and (#traces eq 0 or #{#v: v in traces} eq 1);
        num_traces := #traces gt 0 select #traces[1] else 0;
        if not IsDefined(OT,N) then G,T := CharacterOrbitReps(N:RepTable); OT[N] := <G,T>; end if;
        chi := OT[N][1][o];
        M := Conductor(chi);
        if not IsDefined(OT,M) then G,T := CharacterOrbitReps(M:RepTable); OT[M] := <G,T>; end if;
        odd_weight := IsOdd(k) select 1 else 0;
        is_real := IsReal(chi) select 1 else 0;
        n := Order(chi);
        u := UnitGenerators(chi);
        clist := eval(ConreyTable[[N,o]]);
        v := [Integers()|n*a : a in ConreyCharacterAngles(N,clist[1],u)];
        char_values := <N,n,u,v>;
        psi := AssociatedPrimitiveCharacter(chi);
        po := OT[M][2][psi];
        label := NewspaceLabel(N,k,o);
        sdims := DT[[N,k,o]];
        dS := sdims[1];  dE := sdims[2];  dNS := sdims[3]; dNE := sdims[4]; dM:=dS+dE; dNM:= dNS+dNE;
        if dNE lt 0 then dNE := "\\N"; dNM := "\\N"; end if;
        assert dNS eq sum(dims);
        trace_bound := 1;
        while #{traces[n][1..trace_bound]:n in [1..#traces]} lt num do
            trace_bound +:= 1;
            if trace_bound gt num_traces then
                print "*** Unable to determine trace bound for space %o:%o:%o:%o, tr(a_n) for n <= %o are not distinct ***\n", N, k, o, dims, Min([#t:t in traces]);
                trace_bound := "\\N";
            end if;
        end while;
        P := PrimeDivisors(N);
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
            plus_dim := sum([a[2]:a in AL_dims|prod([b[2]:b in a[1]]) eq 1]);
        else
            AL_dims:="\\N";
            plus_dim := "\\N";
        end if;
        str := strip(Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o",
                label,N,prod(P),P,k,odd_weight,analytic_conductor,N*k^2,o,Base26Encode(o-1),ConreyTable[[N,o]],Order(chi),
                Conductor(chi),po,Degree(chi),Parity(chi),is_real,char_values,SturmBound(N,k),trace_bound,dNS,#dims,dims,dE,dNE,dS,dM,dNM,AL_dims,plus_dim));
        str := SubstituteString(str,"<","[");  str:= SubstituteString(str,">","]");
        if Detail gt 0 then print str; else if Detail ge 0 then print label; end if; end if;
        Puts(outfp,str);
        cnt +:= 1;
    end for;
    printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start;
end procedure;

procedure LookupFields (infile,field_labels)
    R<x>:=PolynomialRing(Integers());
    start:=Cputime();
    S:=Split(Read(field_labels),"\n");  // format is coeffs:label
    FieldTable:=AssociativeArray();
    for s in S do r:=Split(s,":"); FieldTable[eval(r[1])]:= r[2]; end for;
    printf "Loaded %o records from field label file %o in %o secs.\n", #Keys(FieldTable), field_labels, Cputime()-start;
    S := Split(Read(infile),"\n");
    printf "Loaded %o records from input file %o in %o secs.\n", #S, infile, Cputime()-start;
    start:=Cputime();
    OT := AssociativeArray();
    unknown_fields := {};
    nopolredabs_fields := {};
    cnt := 0;  unknown_cnt := 0;  nopolredabs_cnt := 0;
    for s in S do
        r := <eval(a):a in Split(s,":")>;
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
    
from lmfdb.db_backend import db
for k in sorted(db.mf_newforms.col_type.keys()):
    print '["%s","%s"],'%(k,db.mf_newforms.col_type[k])
*/
newform_columns := [
<"Nk2","integer", true>,
<"analytic_conductor","double precision", true>,
<"analytic_rank","smallint", false>,
<"analytic_rank_proved","boolean",false>,
<"artin_degree","integer", false>,
<"artin_field","jsonb", false>,
<"artin_field_label","text", false>,
<"artin_image","text", false>,
<"atkin_lehner_eigenvals","jsonb", false>,
<"atkin_lehner_string","text", false>,
<"char_conductor","integer", true>,
<"char_degree","integer", true>,
<"char_is_real","boolean", true>,
<"char_labels","jsonb", true>,
<"char_orbit_index","integer", true>,
<"char_orbit_label","text", true>,
<"char_order","integer", true>,
<"char_parity","smallint", true>,
<"char_values","jsonb",true>,
<"cm_discs","jsonb", false>,
<"dim","integer", false>,
<"field_disc","numeric",false>,
<"field_poly","jsonb", false>,
<"field_poly_is_cyclotomic","boolean", false>,
<"field_poly_is_real_cyclotomic","boolean", false>,
<"field_poly_root_of_unity","integer", false>,
<"fricke_eigenval","smallint", false>,
<"has_inner_twist","smallint",false>,
<"hecke_cutters","jsonb", false>,
<"hecke_orbit","integer", false>,
<"hecke_orbit_code","bigint", false>,
<"hecke_ring_character_values","json", false>,
<"hecke_ring_denominators","jsonb", false>,
<"hecke_ring_generator_nbound","integer",false>,
<"hecke_ring_index","numeric", false>,
<"hecke_ring_index_factorization","jsonb", false>,
<"hecke_ring_index_proved","boolean", false>,
<"hecke_ring_inverse_denominators","jsonb", false>,
<"hecke_ring_inverse_numerators","jsonb", false>,
<"hecke_ring_numerators","jsonb", false>,
<"hecke_ring_power_basis","boolean", false>,
<"inner_twist","jsonb", false>,
<"inner_twist_count","integer", false>,
<"is_cm","boolean", false>,
<"is_polredabs","boolean", false>,
<"is_rm","boolean", false>,
<"is_self_dual","boolean", false>,
<"is_self_twist","boolean", false>,
<"is_twist_minimal","boolean", false>,
<"label","text", false>,
<"level","integer", true>,
<"level_primes","jsonb", true>,
<"level_radical","integer", true>,
<"nf_label","text", false>,
<"odd_weight","boolean", true>,
<"prim_orbit_index","integer", true>,
<"projective_field","jsonb", false>,
<"projective_field_label","text", false>,
<"projective_image","text", false>,
<"projective_image_type","text", false>,
<"qexp_display","text", false>,
<"qexp_prec","smallint", false>,
<"related_objects","jsonb", false>,
<"rm_discs","jsonb", false>,
<"self_twist_discs","jsonb", false>,
<"self_twist_proved","boolean", false>,
<"self_twist_type","smallint", false>,
<"space_label","text", true>,
<"trace_display","jsonb", false>,
<"trace_hash","bigint", false>,
<"trace_moments","jsonb", false>,
<"trace_zratio","numeric", false>,
<"traces","jsonb", false>,
<"weight","smallint", true>
];

procedure FormatNewformData (infile, outfile, conrey_labels, field_labels, analytic_ranks, artin_reps: Detail:=0, Jobs:=1, JobId:=0)
    assert Jobs gt 0 and JobId ge 0 and JobId lt Jobs;
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    R<x>:=PolynomialRing(Integers());
    start:=Cputime();
    S := Split(Read(conrey_labels),"\n"); // format is N:o:[n1,n2,...] (list of conrey chars chi_N(n,*) in orbit o for modulus N)
    ConreyTable:=AssociativeArray();
    for s in S do r:=Split(s,":"); ConreyTable[[StringToInteger(r[1]),StringToInteger(r[2])]] := r[3]; end for;
    printf "Loaded %o records from conrey label file %o in %o secs.\n", #Keys(ConreyTable), conrey_labels, Cputime()-start;
    S:=Split(Read(field_labels),"\n");  // format is coeffs:label
    FieldTable:=AssociativeArray();
    for s in S do r:=Split(s,":"); FieldTable[eval(r[1])]:= r[2]; end for;
    printf "Loaded %o records from field label file %o in %o secs.\n", #Keys(FieldTable), field_labels, Cputime()-start;
    S:=Split(Read(analytic_ranks),"\n");  // format is label:rank
    RankTable:=AssociativeArray();
    for s in S do r:=Split(s,":"); RankTable[r[1]]:= [StringToInteger(r[2]),StringToInteger(r[3])]; end for;
    printf "Loaded %o records from analytic rank file %o in %o secs.\n", #Keys(RankTable), analytic_ranks, Cputime()-start;
    S:=Split(Read(artin_reps),"\n");  // format is level:weight:label:artin_label:discs:ptype:pname:ppoly:deg:id:poly:th:tzr,tzm
    ArtinTable:=AssociativeArray();
    for s in S do r:=Split(s,":"); ArtinTable[r[3]]:= r; end for;
    printf "Loaded %o records from Artin rep file %o in %o secs.\n", #Keys(ArtinTable), artin_reps, Cputime()-start;
    S := Split(Read(infile),"\n");
    printf "Loaded %o records from input file %o in %o secs.\n", #S, infile, Cputime()-start;
    start:=Cputime();
    outfp := Open(outfile,"w");
    if JobId eq 0 then
        headfp := Jobs gt 1 select Open("mf_newforms_header.txt","w") else outfp;
        labels := Join([r[1]:r in newform_columns],":");
        types := Join([r[2]:r in newform_columns],":");
        Puts(headfp,labels);  Puts(headfp,types); Puts(headfp,"");
        Flush(headfp); delete(headfp);
    end if;
    OT := AssociativeArray();
    unknown_fields := {};
    nopolredabs_fields := {};
    cnt := 0;  unknown_cnt := 0;  nopolredabs_cnt := 0;
    rec := AssociativeArray();
    for c in newform_columns do rec[c[1]] := "\\N"; end for;
    RCP := AssociativeArray();  RCPI := AssociativeArray();
    for s in S do
        N := StringToInteger(Substring(s,1,Index(s,":")-1));
        if ((N-JobId) mod Jobs) ne 0 then continue; end if;
        for c in newform_columns do rec[c[1]] := "\\N"; end for;
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
        P := PrimeDivisors(N);
        rec["level_primes"] := P;
        rec["level_radical"] := prod(P);
        rec["weight"] := k;
        rec["char_orbit_index"] := o;
        rec["analytic_conductor"] := AnalyticConductor(N,k);
        rec["odd_weight"] := IsOdd(k) select 1 else 0;
        if not IsDefined(OT,N) then G,T := CharacterOrbitReps(N:RepTable); OT[N] := <G,T>; end if;
        chi := OT[N][1][o];
        M := Conductor(chi);
        if not IsDefined(OT,M) then G,T := CharacterOrbitReps(M:RepTable); OT[M] := <G,T>; end if;
        rec["char_conductor"] := M;
        rec["prim_orbit_index"] := OT[M][2][AssociatedPrimitiveCharacter(chi)];
        rec["space_label"] := NewspaceLabel(N,k,o);
        rec["char_orbit_label"] := Base26Encode(o-1);
        rec["char_order"] := Order(chi);
        rec["char_labels"] := ConreyTable[[N,o]];
        rec["char_parity"] := Parity(chi);
        rec["char_is_real"] := IsReal(chi) select 1 else 0;
        rec["char_degree"] := Degree(chi);
        n := Order(chi);
        u := UnitGenerators(chi);
        clist := eval(ConreyTable[[N,o]]);
        v := [Integers()|n*a : a in ConreyCharacterAngles(N,clist[1],u)];
        rec["char_values"] := <N,n,u,v>;
        m := #[d:d in dims|d eq 1];
        for n := 1 to #dims do
            // clear columns that are not space invariant
            for c in newform_columns do if not c[3] then rec[c[1]] := "\\N"; end if; end for;
            rec["hecke_orbit"] :=n;
            rec["dim"] := dims[n];
            label := NewformLabel(N,k,o,n);
            rec["label"] := label;
            rec["hecke_orbit_code"] := HeckeOrbitCode(N,k,o,n);
            rec["trace_display"] := [r[6][n][2],r[6][n][3],r[6][n][5],r[6][n][7]];
            rec["traces"] := r[6][n];
            if o eq 1 then
                rec["atkin_lehner_eigenvals"] := r[7][n];
                rec["fricke_eigenval"] := prod([a[2]:a in r[7][n]]);
                rec["atkin_lehner_string"] := #r[7][n] gt 0 select &cat[a[2] eq 1 select "+" else "-" : a in r[7][n]] else "";
            end if;
            if IsDefined(RankTable,label) and RankTable[label][1] ge 0 then
                rec["analytic_rank"] := RankTable[label][1];
                rec["analytic_rank_proved"] := RankTable[label][2];
            end if;
            rec["self_twist_proved"] := r[11][n][1];
            std := r[11][n][2];
            assert #std in [0,1,3] and (#std lt 3 or k eq 1);
            rec["self_twist_discs"] := Sort(std,func<a,b|Abs(b)-Abs(a)>);
            rec["cm_discs"] := Sort([d:d in std|d lt 0],func<a,b|Abs(b)-Abs(a)>);
            rec["rm_discs"] := Sort([d:d in std|d gt 0],func<a,b|Abs(b)-Abs(a)>);
            rec["is_self_twist"] := #std gt 0 select 1 else 0; 
            rec["is_cm"] := #[d:d in std|d lt 0] gt 0 select 1 else 0; 
            rec["is_rm"] := #[d:d in std|d gt 0] gt 0 select 1 else 0;
            if #std eq 3 then rec["self_twist_type"] := 3; else if #std eq 0 then rec["self_twist_type"] := 0; else rec["self_twist_type"] := std[1] lt 0 select 1 else 2; end if; end if;
            if n le #r[12] then
                rec["inner_twist"] := r[12][n];
                rec["inner_twist_count"] := sum([t[2]: t in r[12][n]]);
                rec["has_inner_twist"] := rec["inner_twist_count"] gt 0 select 1 else 0;
            else
                rec["inner_twist_count"] := -1;
                rec["has_inner_twist"] := -1;
            end if;
            ro := (k eq 2 and o eq 1 and dims[n] eq 1) select [Sprintf("\"EllipticCurve/Q/%o/%o\"",N,Base26Encode(n-1))] else [];
            if IsDefined(ArtinTable,label) then
                ar := ArtinTable[label];
                if ar[4] ne "?" then Append(~ro,"\"ArtinRepresentation/" cat ar[4] cat "c1\""); end if;
                D := eval(ar[5]);
                assert Set(D) eq Set(std);
                rec["projective_image_type"] := ar[6];
                rec["projective_image"] := ar[7];
                if #ar ge 8 and ar[8] ne "[]" then
                    f := eval(ar[8]);  assert #f gt 1;
                    rec["projective_field"] := f;
                    if IsDefined(FieldTable,f) then
                        rec["projective_field_label"] :=FieldTable[f];
                    else
                        if not f in unknown_fields then Include(~unknown_fields,f); PrintFile("unknown_fields.txt",sprint(f)); unknown_cnt +:= 1; end if;
                    end if;
                end if;
                if #ar ge 9 then rec["artin_degree"] := ar[9]; end if;
                if #ar ge 10 then rec["artin_image"] := ar[10]; end if;
                if #ar ge 11 and ar[11] ne "[]" then 
                    f:=eval(ar[11]);  assert #f gt 1;
                    rec["artin_field"] := f;
                    if IsDefined(FieldTable,f) then
                        rec["artin_field_label"] := FieldTable[f];
                    else
                        if not f in unknown_fields then Include(~unknown_fields,f); PrintFile("unknown_fields.txt",sprint(f)); unknown_cnt +:= 1; end if;
                    end if;
                end if;
                if #ar ge 12 then
                    rec["trace_zratio"] := ar[12];
                    rec["trace_moments"] := ar[13];
                    rec["trace_hash"] := ar[14];
                end if;
            end if;
            rec["related_objects"] := ro;
            f := 0;
            if n le #r[8] then
                f := r[8][n];
                assert #f eq dims[n]+1;
                rec["field_poly"] := f;
                if #f eq 2 then rec["field_disc"] := 1; end if;
                zb,zn := IsCyclotomicPolynomial(R!f);
                rec["field_poly_is_cyclotomic"] := zb select 1 else 0;
                if not zb then
                    for m in EulerPhiInverse(dims[n]) do if not IsDefined(RCP,m) then RCP[m]:=RealCyclotomicPolynomial(m); RCPI[RCP[m]]:=m; end if; end for;
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
                else
                    if not f in nopolredabs_fields then Include(~nopolredabs_fields,f); PrintFile("nopolredabs_fields.txt",sprint(f)); nopolredabs_cnt +:= 1; end if;
                end if;
                if #r[14] ge n then rec["trace_zratio"] := Sprintf("%.3o",r[14][n]); end if;
                if #r[15] ge n then rec["trace_moments"] := [Sprintf("%.3o",m):m in r[15][n]]; end if;
                if #r[16] ge n then rec["trace_hash"] := r[16][n]; end if;
            end if;
            if n le #r[9] then rec["hecke_cutters"] := r[9][n]; end if;
            rec["is_self_dual"] := r[18][n];
            if n gt m and n-m le #r[10] then
                nn := n-m;
                assert f eq r[10][nn][1];
                assert #r[10][nn][2] eq dims[n];
                dens := [Integers()|LCM([Denominator(x):x in r[10][nn][2][i]]):i in [1..dims[n]]];
                nums := [[Integers()|dens[i]*x:x in r[10][nn][2][i]]:i in [1..dims[n]]];
                rec["hecke_ring_denominators"] := dens;
                rec["hecke_ring_numerators"] := nums;
                rec["hecke_ring_generator_nbound"] := r[10][nn][7];
                rec["hecke_ring_power_basis"] := (dens eq [1:i in [1..dims[n]]] and nums eq [[i eq j select 1 else 0:i in [1..dims[n]]]:j in [1..dims[n]]]) select 1 else 0;
                rec["hecke_ring_index"] := r[10][nn][3];
                rec["hecke_ring_index_factorization"] := Factorization(r[10][nn][3]);
                rec["hecke_ring_index_proved"] := r[10][nn][4] eq 0 select 0 else 1;
                rec["qexp_prec"] := #r[10][nn][5]+2;
                rec["qexp_display"] := qExpansionStringOverNF(r[10][nn][5],10);
                dd := dims[n];
                A := (GL(dd,Rationals())!Matrix(r[10][nn][2]))^-1;
                A := [[A[i][j]:j in [1..dd]]:i in [1..dd]];
                idens := [LCM([Denominator(x):x in A[i]]):i in [1..#A]];
                rec["hecke_ring_inverse_denominators"] := idens;
                rec["hecke_ring_inverse_numerators"] := [[idens[i]*x:x in A[i]]:i in [1..#A]];
                if o gt 1 then rec["hecke_ring_character_values"] := [<r[10][nn][6][1][i],r[10][nn][6][2][i]> : i in [1..#r[10][nn][6][1]]]; end if;
                if r[10][nn][7] ne 0 then rec["field_disc"] := r[10][nn][7]; end if;
            else
                if o gt 1 and n le #r[17] then rec["hecke_ring_character_values"] := [<r[17][n][1][i],r[17][n][2][i]>:i in [1..#r[17][n][1]]]; end if;
                if dims[n] le m then
                    rec["qexp_display"] := qExpansionStringOverQ(r[6][n],10);
                    rec["qexp_prec"] := #r[6][n];
                end if;
            end if;
            assert Sort([x:x in Keys(rec)]) eq [t[1]: t in newform_columns];
            str := Join([sprint(rec[t[1]]):t in newform_columns],":");
            str := SubstituteString(str,"<","[");  str := SubstituteString(str,">","]");
            if Detail gt 0 then print str; else if Detail ge 0 then print label; end if; end if;
            Puts(outfp,str);
            cnt +:= 1;
        end for;
    end for;
    printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start;
    if unknown_cnt gt 0 then printf "Appended %o unknown polredabs field polys to unknown_fields.txt\n", unknown_cnt; end if;
    if nopolredabs_cnt gt 0 then printf "Appended %o no polredabs field polys to nopolredabs_fields.txt\n", nopolredabs_cnt; end if;
end procedure;

procedure FormatHeckeNFData (infile, outfile: Detail:=0)
    start := Cputime();
    S := Split(Read(infile),"\n");
    printf "Loaded %o records from input file %o in %o secs.\n", #S, infile, Cputime()-start;
    start := Cputime();
    outfp := Open(outfile,"w");
    Puts(outfp,"hecke_orbit_code:n:an:trace_an");
    Puts(outfp,"bigint:integer:jsonb:numeric");
    Puts(outfp,"");
    cnt := 0;
    for s in S do
        r := <eval(a):a in Split(s,":")>;
        N := r[1]; k := r[2]; o := r[3]; dims := r[5];
        off := #[d:d in dims|d eq 1];
        for i := 1 to #dims do
            code := HeckeOrbitCode(N,k,o,i);
            if i gt off and (i-off) le #r[10] then
                E := r[10][i-off];
                assert #E[5] ge 1000;
                a := NFSeq(E[1],E[2],E[5]);
                for n := 1 to 1000 do
                    an := r[10][i-off][5][n];
                    trace_an := r[6][i][n];
                    assert Trace(a[n]) eq trace_an;
                    str := strip(Sprintf("%o:%o:%o:%o",code,n,an,trace_an));
                    str := SubstituteString(str,"<","[");  str := SubstituteString(str,">","]");
                    if Detail gt 0 then print str; end if;
                    Puts(outfp,str);  cnt +:= 1;
                end for;
            else
                assert #r[6][i] eq 1000;
                for n := 1 to 1000 do
                    trace_an := r[6][i][n];
                    an := dims[i] eq 1 select [trace_an] else "\\N";
                    str := strip(Sprintf("%o:%o:%o:%o",code,n,an,trace_an));
                    str := SubstituteString(str,"<","[");  str := SubstituteString(str,">","]");
                    if Detail gt 0 then print str; end if;
                    Puts(outfp,str);  cnt +:= 1;
                end for;
            end if;
            if Detail ge 0 then printf "Created eignenvalue data for form %o:%o:%o:%o\n",N,k,o,i; end if;
        end for;
    end for;
    printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start;
end procedure;

function CompareCCLists(a,b)
    for i:=1 to #a do
        if Real(a[i]) lt Real(b[i]) then return -1; end if;
        if Real(a[i]) gt Real(b[i]) then return 1; end if;
        if Imaginary(a[i]) lt Imaginary(b[i]) then return -1; end if;
        if Imaginary(a[i]) gt Imaginary(b[i]) then return 1; end if;
    end for;
    return 0;
end function;

// Round real and imaginary parts of complex number z to accuracty of 1/absprec (so values within 1/(2*absprec) will come out the same)
function RoundCC(z,absprec)
    return Round(absprec*Real(z))/absprec + Round(absprec*Imaginary(z))/absprec * Parent(z).1;
end function;

// if SatakeAngle is set, convert -0.5 to 0.5
function sprintreal(x,prec:SatakeAngle:=false)
    if Abs(x) lt 10^10 and prec ge 20 and Abs(x-BestApproximation(x,1000)) lt 10^-(prec-1) then x := RealField(prec)!BestApproximation(x,1000); end if;
    s := Sprintf("%o",x);
    if "." in s and not "e" in s and not "E" in s then i:=#s; while s[i] eq "0" do i-:=1; end while; s := Substring(s,1,i); if s[#s] eq "." then Prune(~s); end if; if s eq "-0" then s:="0"; end if; end if;
    if SatakeAngle and s eq "-0.5" then s := "0.5"; end if;
    return s;
end function;
    
// Given ap, chi(p), p, and k, Satake parameters alpha_p are reciprocal roots of Lp(t/p^((k-1)/2))= 1 - ap/p^((k-1)/2)*t + chi(p)*t^2 (so Lp(t) = 1 - ap*t + chi(p)*p^(k-1)t^2)
// The Satake angles are theta_p = Arg(alpha_p)/(2*pi) in (-0.5,0.5], we take the smaller value.
function SatakeAngle(ap,chip,p,k,pi)
    q := p^(k-1);
    // apply quadratic formula (inverted to take reciprocal root
    alpha1 := (2*chip) / (ap/Sqrt(q) + Sqrt(ap^2/q - 4*chip));
    alpha2 := (2*chip) / (ap/Sqrt(q) - Sqrt(ap^2/q - 4*chip));
    thetas := [Real(Arg(alpha1))/(2*pi),Real(Arg(alpha2))/(2*pi)];
    assert &and[theta ge -0.5 and theta le 0.5: theta in thetas];
    thetas := Sort(thetas);
    if thetas[1] eq -0.5 then thetas[1] := 0.5; end if;
    thetas := Sort(thetas);
    return thetas[1];
end function;


procedure FormatHeckeCCData (infile, outfile, conrey_labels: Precision:=20, DegreeBound:=0, Detail:=0, Jobs:=1, JobId:=0)
    assert Jobs gt 0 and JobId ge 0 and JobId lt Jobs;
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    start:=Cputime();
    S:=Split(Read(conrey_labels),"\n"); // format is N:o:[n1,n2,...] (list of conrey chars chi_N(n,*) in orbit o for modulus N)
    ConreyTable:=AssociativeArray();
    for s in S do r:=Split(s,":"); ConreyTable[[StringToInteger(r[1]),StringToInteger(r[2])]] := eval(r[3]); end for;
    printf "Loaded %o records from conrey label file %o in %o secs.\n", #Keys(ConreyTable), conrey_labels, Cputime()-start;
    start := Cputime();
    S := Split(Read(infile),"\n");
    printf "Loaded %o records from input file %o in %o secs.\n", #S, infile, Cputime()-start;
    start:=Cputime();
    outfp := Open(outfile,"w");
    if JobId eq 0 then
        headfp := Jobs gt 1 select Open("mf_hecke_cc_header.txt","w") else outfp;
        Puts(headfp,"hecke_orbit_code:lfunction_label:conrey_label:embedding_index:embedding_m:embedding_root_real:embedding_root_imag:an:angles");
        Puts(headfp,"bigint:text:integer:integer:integer:double precision:double precision:jsonb:jsonb");
        Puts(headfp,"");
        Flush(headfp); delete(headfp);
    end if;
    cnt := 0;
    prec := 2*Precision+1;
    CC := ComplexField(prec);
    RR := RealField(prec);
    pi := Pi(RR);
    T := AssociativeArray(Integers());
    for s in S do
        N := StringToInteger(Substring(s,1,Index(s,":")-1));
        if ((N-JobId) mod Jobs) ne 0 then continue; end if;
        r := Split(s,":");
        if r[5] eq "[]" then continue; end if;
        r := <eval(a):a in r>;
        N := r[1]; k := r[2]; o := r[3]; dims := r[5];
        if not IsDefined(T,N) then T[N] := CharacterOrbitReps(N); end if;
        chi := T[N][o];
        space_label := Sprintf("%o.%o.%o",N,k,Base26Encode(o-1));
        L := ConreyTable[[r[1],r[3]]];
        off := #[d:d in dims|d eq 1];
        for i := 1 to #dims do
            if DegreeBound gt 0 and dims[i] gt DegreeBound then
                printf "Skipping form %o:%o:%o:%o because its dimension %o exceeds the specified degree bound %o.\n",N,k,o,i,dims[i],DegreeBound;
                break;
            end if;
            t := Cputime();
            label := space_label cat "." cat Base26Encode(i-1);
            if i-off gt #r[10] then
                printf "Skipping form %o:%o:%o:%o because eignvalue data is not available.\n",N,k,o,i;
                break;
            end if;
            if i gt #r[17] then 
                printf "Skipping form %o:%o:%o:%o because character value data is not available.\n",N,k,o,i;
                break;
            end if;
            code := HeckeOrbitCode(N,k,o,i);
            if i gt off then X := r[10][i-off]; a := NFSeq(X[1],X[2],X[5]); K := Parent(a[1]); else a := r[6][i]; K := Rationals(); end if;
            assert #a ge 1000;
            xi := CharacterFromValues(N,r[17][i][1],[K|z:z in r[17][i][2]]);
            d := Degree(K);
            // use more precision here, we need to be sure to separate conjugates
            E := d gt 1 select LabelEmbeddings(a,ConreyConjugates(chi,xi:ConreyLabelList:=L):Precision:=Max(prec,100)) else [[L[1],1]];
            c := ExactQuotient(d,#L);
            root := d gt 1 select Conjugates(Parent(a[1]).1:Precision:=prec) else [CC!0];
            A := [Conjugates(a[n]:Precision:=prec):n in [1..1000]];
            P := [p:p in PrimesInInterval(1,1000)|GCD(N,p) eq 1];
            firstP := #[p:p in P|p lt 100];
            C := [Conjugates(xi(p):Precision:=prec):p in P];
            for m := 1 to d do
                e := E[m];
                lfunc_label := Sprintf("%o.%o.%o",label,e[1],e[2]);
                embedding_m := (Index(L,e[1])-1)*c + e[2];
                an := [[sprintreal(Real(A[n][m]),Precision),sprintreal(Imaginary(A[n][m]),Precision)] : n in [1..1000]];
                angles := [[Sprintf("%o",P[j]),sprintreal(SatakeAngle(A[P[j]][m],C[j][m],P[j],k,pi),Precision)]:j in [1..#P]];
            // putt curly braces around arrays
                str := strip(Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o",code,lfunc_label,e[1],e[2],embedding_m,sprintreal(Real(root[m]),Precision),sprintreal(Imaginary(root[m]),Precision),an,angles));
                str := SubstituteString(str,"<","[");  str := SubstituteString(str,">","]");
                if Detail gt 0 then print str; end if;
                Puts(outfp,str);  cnt +:= 1;
            end for;
            if Detail ge 0 then printf "Created eignenvalue data for form %o:%o:%o:%o(%o) of dimension %o in %os (%os)\n",N,k,o,i,label,d,Cputime()-t,Cputime()-start; end if;
        end for;
        Flush(outfp);
    end for;
    printf "Wrote %o records to %o in %o secs\n", cnt, outfile, Cputime()-start;
end procedure;
            
procedure CreateSubspaceData (outfile, conrey_labels, dimfile: Detail:=0)
    start:=Cputime();
    S:=Split(Read(conrey_labels),"\n"); // format is N:o:[n1,n2,...] (list of conrey chars chi_N(n,*) in orbit o for modulus N)
    ConreyTable:=AssociativeArray();
    for s in S do r:=Split(s,":"); ConreyTable[[StringToInteger(r[1]),StringToInteger(r[2])]] := r[3]; end for;
    printf "Loaded %o records from conrey label file %o in %o secs.\n", #Keys(ConreyTable), conrey_labels, Cputime()-start;
    start:=Cputime();
    S := [Split(r,":"): r in Split(Read(dimfile),"\n")];
    S := [[StringToInteger(a):a in r]:r in S];
    DT := AssociativeArray();
    B := 0;
    for r in S do DT[[r[1],r[2],r[3]]]:=[r[4],r[6]]; B := Max(B,r[1]); end for;
    printf "Loaded %o records from dimension file %o in %os, set B to %o\n", #S, dimfile, B, Cputime()-start;
    delete S;
    start := Cputime();
    outfp := Open(outfile,"w");
    Puts(outfp,"label:level:weight:char_orbit_index:char_orbit_label:char_labels:dim:sub_label:sub_level:sub_char_orbit_index:sub_char_orbit_label:sub_char_labels:sub_dim:sub_mult");
    Puts(outfp,"text:integer:smallint:integer:text:jsonb:integer:text:integer:integer:text:jsonb:integer:integer");
    Puts(outfp,"");
    A := [];
    NewDimTable := AssociativeArray();
    id := 0;
    for N in [1..Floor(B)] do
        t := Cputime();
        G,T := CharacterOrbitReps(N:RepTable);
        A[N] := <G,T>;
        for i:=1 to #G do
            i_label := Base26Encode(i-1);
            chi := G[i];
            psi := AssociatedPrimitiveCharacter(chi);
            C := Modulus(psi);
            subs := [*<M,#Divisors(ExactQuotient(N,M)),A[M][2][schi],schi> where schi:=FullDirichletGroup(M)!psi where M := C*D : D in Divisors(ExactQuotient(N,C))*];
            for k in [1..Floor(Sqrt(B/N))] do
                dim := DT[[N,k,i]][1];  newdim := DT[[N,k,i]][2];
                dims := [DT[[sub[1],k,sub[3]]][2] : sub in subs];
                mults := [sub[2]: sub in subs];
                assert &+[dims[n]*mults[n]: n in [1..#subs]] eq dim;
                label := NewspaceLabel(N,k,i);
                for n:=1 to #subs do
                    if dims[n] eq 0 then continue; end if;
                    id +:= 1;
                    M := subs[n][1];
                    j := A[M][2][subs[n][4]];
                    j_label := Base26Encode(j-1);
                    sub_label := NewspaceLabel(M,k,j);
                    str := strip(Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o",
                            label,N,k,i,i_label,ConreyTable[[N,i]],dim,sub_label,M,j,j_label,ConreyTable[[M,j]],dims[n],mults[n]));
                    if Detail gt 0 then print str; end if;
                    Puts(outfp,str);
                end for;
            end for;
        end for;
        printf "Time to complete level %o was %os (%os)\n", N,Cputime()-t,Cputime()-start;
        Flush(outfp);
    end for;
    printf "Wrote %o records to %o in %o secs\n", id, outfile, Cputime()-start;
end procedure;
                
procedure CreateGamma1SubspaceData (outfile, dimfile: Detail:=0)
    start := Cputime();
    S := [Split(r,":"): r in Split(Read(dimfile),"\n")];
    S := [[StringToInteger(a):a in r]:r in S];
    DT := AssociativeArray();
    B := 0;
    for r in S do DT[[r[1],r[2],r[3]]]:=[r[4],r[6]]; B := Max(B,r[1]); end for;
    printf "Loaded %o records from dimension file %o in %os, set B to %o\n", #S, dimfile, B, Cputime()-start;
    start := Cputime();
    outfp := Open(outfile,"w");
    Puts(outfp,"label:level:weight:dim:sub_level:sub_dim:sub_mult");
    Puts(outfp,"text:integer:smallint:integer:integer:integer:integer");
    Puts(outfp,"");
    // Computing dimensions of cuspidal and new cuspidal subspaces of Gamma1 is quick so we do it on the fly
    T := AssociativeArray();
    id := 0;
    for N in [1..B] do
        oN := NumberOfCharacterOrbits(N);
        t := Cputime();
        subs := [<M,#Divisors(ExactQuotient(N,M))> : M in Divisors(N)];
        for k in [1..Floor(Sqrt(B/N))] do
            dim := &+[DT[[N,k,i]][1]:i in [1..oN]];
            newdim := &+[DT[[N,k,i]][2]:i in [1..oN]];
            if k gt 1 then assert dim eq DimensionCuspFormsGamma1(N,k) and newdim eq DimensionNewCuspFormsGamma1(N,k); end if;
            assert dim - newdim eq sum([T[[sub[1],k]]*sub[2] : sub in subs | sub[1] ne N]);
            T[[N,k]] := newdim;
            dims := [T[[sub[1],k]] : sub in subs];
            mults := [sub[2]: sub in subs];
            assert &+[dims[n]*mults[n]: n in [1..#subs]] eq dim;
            for n:=1 to #subs do
                if dims[n] eq 0 then continue; end if;
                id +:= 1;
                str := strip(Sprintf("%o.%o:%o:%o:%o:%o:%o:%o", N,k,N,k,dim,subs[n][1],dims[n],mults[n]));
                if Detail gt 0 then print str; end if;
                Puts(outfp,str);
            end for;
        end for;
        printf "Time to complete Gamma1 level %o was %os (%os)\n", N,Cputime()-t,Cputime()-start;
        Flush(outfp);
    end for;
    printf "Wrote %o records to %o in %o secs\n", id, outfile, Cputime()-start;
end procedure;

// infile should have records formatted as N:k:i:D:... where D is a vector of dimensions of newforms, only needed for k=1, but will verify other dimensions
procedure CreateDimensionTable(infile,outfile:Detail:=0,Jobs:=1,JobId:=0)
    assert Jobs gt 0 and JobId ge 0 and JobId lt Jobs;
    if Jobs ne 1 then outfile cat:= Sprintf("_%o",JobId); end if;
    start := Cputime();
    S := Split(Read(infile),"\n");
    A := AssociativeArray();
    B := 0;
    for s in S do
        r := Split(s,":");
        N := StringToInteger(r[1]);  k := StringToInteger(r[2]);  o:= StringToInteger(r[3]); D := eval(r[4]);
        A[[N,k,o]]:= sum(D);
        if N*k*k gt B then B := N*k*k; end if;
    end for;
    printf "Loaded %o records from input file %o in %os, set B to %o\n", #S, infile, Cputime()-start, B;
    delete S;
    O := AssociativeArray();
    fp := Open(outfile,"w");
    for N:=1 to B do
        if ((N-JobId) mod Jobs) ne 0 then continue; end if;
        n := 0; start := Cputime();
        G,T := CharacterOrbitReps(N:RepTable);
        O[N] := T;
        for o:=1 to #G do
            chi := G[o];
            psi := AssociatedPrimitiveCharacter(chi);
            C := Modulus(psi);
            subN := [C*D:D in Divisors(ExactQuotient(N,C))];
            for M in subN do if not IsDefined(O,M) then O[M] := T where _,T:=CharacterOrbitReps(M:RepTable); end if; end for;
            subs := [*<M,O[M][FullDirichletGroup(M)!psi],#Divisors(ExactQuotient(N,M))> : M in subN *];
            for k:=1 to Floor(Sqrt(B/N)) do
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
                Puts(fp,strip(Sprintf("%o:%o:%o:%o:%o:%o:%o\n",N,k,o,dS,dE,dNS,dNE)));
            end for;
        end for;
        Flush(fp);
        printf "Wrote %o records for level %o in %os\n", n, N, Cputime()-start;
    end for;
end procedure;

// You don't want to acutally use this single-threaded procedure, spread the work over multiple cores.
procedure GeneratePostgresDatafiles (B:detail:=0)
    FormatNewspaceData(Sprintf("mfdata_all_%o.txt",B),Sprintf("mf_newspaces_%o.txt",B),Sprintf("conrey_%o.txt",B),Sprintf("mf_all_dims_%o",B):Detail:=detail);
    FormatNewformData(Sprintf("mfdata_all_%o.txt",B),Sprintf("mf_newforms_%o.txt",B),Sprintf("conrey_%o.txt",B),"lmfdb_nf_labels.txt":Detail:=detail);
    FormatHeckeNFData(Sprintf("mfdata_all_%o.txt",B),Sprintf("mf_hecke_nf_%o.txt",B):Detail:=detail);
    FormatHeckeCCData(Sprintf("mfdata_wt1_%o.txt",B),Sprintf("mf_hecke_cc_%o.txt",B),Sprintf("conrey_%o.txt",B):Detail:=detail);
    CreateDimensionTable(Sprintf("mf_all_traces_%o.txt",B),Sprintf("mf_all_dims_%o.txt",B):Detail:=detail);
    CreateSubspaceData(Sprintf("mf_subspaces_%o.txt",B),Sprintf("conrey_%o.txt",B),Sprintf("mf_all_dims_%o",B):Detail:=detail);
    CreateGamma1SubspaceData(Sprintf("mf_gamma1_subspaces_%o.txt",B),Sprintf("mf_all_dims_%o",B):Detail:=detail);
end procedure;

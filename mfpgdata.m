Attach("chars.m");

function sum(X) return #X eq 0 select 0 else &+X; end function;

function SturmBound (N, k)
    return Integers()!Ceiling (Index(Gamma0(N))*k/12);
end function;

alphabet := "abcdefghijklmnopqrstuvwvyz";

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

function qExpansionString(a,prec)
    assert a[1] eq 1;
    s := "q";
    for n:=2 to prec-1 do
        if a[n] ne 0 then
            if a[n] eq 1 then s cat:= Sprintf("+q^%o",n); else
                if a[n] eq -1 then s cat:= Sprintf("-q^%o",n); else
                    if a[n] gt 0 then s cat:= "+"; end if;
                    s cat:= n ge 10 select Sprintf("%oq^{%o}",a[n],n) else Sprintf("%oq^%o",a[n],n); 
                end if;
            end if;
        end if;
    end for;
    s cat:= Sprintf("+O(q^{%o})",prec);
    return StripWhiteSpace(s);
end function;

procedure FormatNewspaceData (infile, outfile: Loud:=false)
    t:=Cputime();
    infp := Open(infile,"r");
    outfp := Open(outfile,"w");
    Puts(outfp,"id:label:level:weight:odd_weight:char_orbit:char_order:cyc_degree:parity:conrey_labels:char_conductor:prim_orbit:sturm_bound:dim:hecke_orbit_dims:eis_dim:eis_new_dim:cusp_dim:mf_dim");
    Puts(outfp,"bigint:text:integer:smallint:boolean:integer:integer:integer:smallint:jsonb:integer:integer:integer:integer:jsonb:integer:integer:integer:integer");
    Puts(outfp,"");
    s := Gets(infp);
    id := 0; oldN := 0;
    while not IsEof(s) do
        id +:=1;
        r := <eval(a):a in Split(s,":")>;
        N := r[1]; k := r[2]; o := r[3]; dims := r[5];
        if N ne oldN then G:=CharacterOrbitReps(N); oldN := N; end if;
        chi := G[o];
        prim_orbit := "\\N"; // TODO: implement and call PrimitiveCharacterOrbitIndex(chi);
        label := Sprintf("%o.%o.%o",N,k,Base26Encode(o-1));
        sturm_bound := HeckeBound(ModularSymbols(chi,k)); // TODO: this is often larger than the sturm bound computed by Sage
        M := ModularForms(chi,k);
        S := CuspidalSubspace(M);
        E := EisensteinSubspace(M);
        NE := NewSubspace(E);
        NS := NewSubspace(S);
        assert sum(dims) eq Dimension(NS);
        str := StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o",id,label,N,k,IsOdd(k) select 1 else 0,o,Order(chi),CharacterFieldDegree(chi),Parity(chi),
                ConreyLabels(chi),Conductor(chi),prim_orbit,sturm_bound,Dimension(NS),dims,Dimension(E),Dimension(NE),Dimension(S),Dimension(M)));
        str := SubstituteString(str,"<","[");  str:= SubstituteString(str,">","]");
        if Loud then print str; end if;
        Puts(outfp,str);
        s := Gets(infp);
    end while;
    printf "Wrote %o records to %o in %o secs\n", id, outfile, Cputime()-t;
end procedure;

procedure FormatNewformData (infile, outfile, polredabsfile: Loud:=false)
    t:=Cputime();
    printf "Loading lmfdb_nf_labes.txt..."; t:=Cputime();
    S:=Split(Read("lmfdb_nf_labels.txt"),"\n"); // forms is p
    A:=AssociativeArray();
    for s in S do r:=Split(s,":"); A[eval(r[1])]:= r[2]; end for;
    printf "took %o secs.\n", Cputime()-t;
    t:=Cputime();
    infp := Open(infile,"r");
    outfp := Open(outfile,"w");
    labels := "id:label:space_label:level:weight:odd_weight:char_orbit:char_order:cyc_degree:parity:conrey_labels:char_conductor";
    types :=  "bigint:text:text:integer:smallint:boolean:integer:integer:integer:smallint:jsonb:integer";
    labels cat:= ":prim_orbit:hecke_orbit:hecke_orbit_code:dim:field_poly:is_polredabs:nf_label:hecke_ring_numerators:hecke_ring_denominators:hecke_ring_index";
    types cat:= ":integer:integer:bigint:integer:jsonb:boolean:text:jsonb:jsonb:jsonb";
    labels cat:= ":hecke_ring_index_proven:trace_hash:qexp_prec:isogeny_class_label:analytic_rank:is_cm:cm_disc:cm_hecke_char:cm_proved:has_inner_twist";
    types cat:= "::boolean:bigint:smallint:text:smallint:smallint:smallint:text:boolean:smallint";
    labels cat:= ":is_twist_minimal:inner_twist:inner_twist_proved:atkin_lehner_eigenvals:hecke_cutters:qexp_display:trace_display";
    types cat:= ":boolean:jsonb:boolean:jsonb:jsonb:text:jsonb";
    Puts(outfp,labels);  Puts(outfp,types); Puts(outfp,"");
    s := Gets(infp);
    id := 0; oldN := 0;
    while not IsEof(s) do
        r := <eval(a):a in Split(s,":")>;
        assert #r ge 13;
        assert #r[5] eq #r[6];
        if r[3] eq 1 then assert #r[5] eq #r[7]; end if;
        assert #r[8] eq #r[11] and #r[8] eq #r[12] and #r[8] eq #r[13];
        N := r[1]; k := r[2]; o := r[3]; dims := r[5];
        if N ne oldN then G:=CharacterOrbitReps(N); oldN := N; end if;
        chi := G[o];
        prim_orbit := "\\N"; // TODO: implement and call PrimitiveCharacterOrbitIndex(chi);
        space_label := Sprintf("%o.%o.%o",N,k,Base26Encode(o-1));
        m := #[d:d in dims|d eq 1];
        for n := 1 to #dims do
            id +:=1;
            label := space_label cat "." cat Base26Encode(n-1);
            isogeny_class_label := (k eq 2 and o eq 1) select Sprintf("%o.%o",N,Base26Encode(n-1)) else "\\N";
            code := HeckeOrbitCode(N,k,o,n);
            trace_display := [r[6][n][2],r[6][n][3],r[6][n][5],r[6][n][7]];
            if dims[n] eq 1 then qexp_display := qExpansionString(r[6][n],10); else qexp_display := "\\N"; end if;
            atkin_lehner := #r[7] gt 0 select r[7][n] else "\\N";
            trace_hash := "\\N";
            analytic_rank := "\\N";
            if n le #r[11] then
                is_cm := r[11][n] ne 0 select 1 else -1;
                cm_disc := r[11][n] eq 0 select "\\N" else r[11][n];
                cm_hecke_char := "\\N"; // TODO: figure out Hecke character label
                cm_proved := 1;
            else
                is_cm := 0;  cm_disc := "\\N";  cm_hecke_char := "\\N";  cm_proved := "\\N";
            end if;
            if n le #r[12] then
                has_inner_twist := #r[12][n] gt 0 select 1 else -1;
                inner_twist := r[12][n];
                is_twist_minimal := "\\N"; // TODO: figure out how to compute this.
                inner_twist_proved := 0;
            else
                has_inner_twist := 0;  inner_twist := "\\N";  is_twist_minimal := "\\N";  inner_twist_proved := "\\N";
            end if;
            embeddings := "\\N";
            if n le #r[8] then
                field_poly := r[8][n];
                if r[13][n] eq 1 then
                    is_polredabs := "1";
                    if IsDefined(A,field_poly) then
                        nf_label := A[field_poly];
                    else
                        nf_label := "\\N";
                        PrintFile("unknown_polredabs_fields.txt",field_poly);
                    end if;
                else
                    polredabs := "0";
                    PrintFile("non_polredabs_fields.txt",field_poly); 
                    nf_label := "\\N";
                end if;
            else
                field_poly := "\\N";
                is_polredabs := "\\N";
                nf_label := "\\N";
            end if;
            hecke_cutters := n le #r[9] select r[9][n] else "\\N";
            if n gt m and n-m le #r[10] then
                nn := n-m;
                assert field_poly eq r[10][nn][1];
                hecke_ring_denominators := [LCM([Denominator(x):x in r[10][nn][2][i]]):i in [1..#r[10][nn][2]]];
                hecke_ring_numerators := [[hecke_ring_denominators[i]*x:x in r[10][nn][2][i]]:i in [1..#r[10][nn][2]]];
                hecke_ring_index := r[10][nn][3]; 
                hecke_ring_index_proven := r[10][nn][4];
                qexp_prec := #r[10][nn][5]+2;
            else
                hecke_ring_denominators := "\\N";
                hecke_ring_numerators := "\\N";
                hecke_ring_index := "\\N";
                hecke_ring_index_proven := "\\N";
                qexp_prec := "\\N";
            end if;
            str := StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o",
                id, label, space_label, N, k, IsOdd(k) select 1 else 0, o, Order(chi), CharacterFieldDegree(chi), Parity(chi), ConreyLabels(chi), Conductor(chi),
                prim_orbit, n, code, dims[n], field_poly, is_polredabs, nf_label, hecke_ring_numerators, hecke_ring_denominators, hecke_ring_index,
                hecke_ring_index_proven, trace_hash, qexp_prec, isogeny_class_label, analytic_rank, is_cm, cm_disc, cm_hecke_char, cm_proved, has_inner_twist,
                is_twist_minimal, inner_twist, inner_twist_proved, atkin_lehner, hecke_cutters, qexp_display, trace_display));
            str := SubstituteString(str,"<","[");  str := SubstituteString(str,">","]");
            if Loud then print str; end if;
            Puts(outfp,str);
        end for;
        s := Gets(infp);
    end while;
    printf "Wrote %o records to %o in %o secs\n", id, outfile, Cputime()-t;
end procedure;

procedure FormatHeckeEigenvalueData (infile, outfile: Loud:=false)
    t:=Cputime();
    infp := Open(infile,"r");
    outfp := Open(outfile,"w");
    Puts(outfp,"id:hecke_orbit_code:n:an:trace_an");
    Puts(outfp,"bigint:bigint:integer:jsonb:numeric");
    Puts(outfp,"");
    s := Gets(infp);
    id := 0; oldN := 0;
    while not IsEof(s) do
        r := <eval(a):a in Split(s,":")>;
        N := r[1]; k := r[2]; o := r[3]; dims := r[5];
        off := #[d:d in dims|d eq 1];
        for i := 1 to #dims do
            code := HeckeOrbitCode(N,k,o,i);
            if i gt off and (i-off) le #r[10] then
                assert #r[10][i-off][5] ge 1000;
                // TDOO: Verify traces!
                for n := 1 to 1000 do
                    id +:= 1;
                    an := r[10][i-off][5][n];
                    trace_an := r[6][i][n];
                    str := StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o",id,code,n,an,trace_an));
                    str := SubstituteString(str,"<","[");  str := SubstituteString(str,">","]");
                    if Loud then print str; end if;
                    Puts(outfp,str);
                end for;
            else
                assert #r[6][i] eq 1000;
                for n := 1 to 1000 do
                    id +:= 1;
                    trace_an := r[6][i][n];
                    an := dims[i] eq 1 select [trace_an] else "\\N";
                    str := StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o",id,code,n,an,trace_an));
                    str := SubstituteString(str,"<","[");  str := SubstituteString(str,">","]");
                    if Loud then print str; end if;
                    Puts(outfp,str);
                end for;
            end if;
        end for;
        s := Gets(infp);
    end while;
    printf "Wrote %o records to %o in %o secs\n", id, outfile, Cputime()-t;
end procedure;
                    
procedure GeneratePostgresDatafiles (B:detail:=false)
    FormatNewspaceData(Sprintf("mfdata_%o.txt",B),Sprintf("mf_newspaces_%o.txt",B):Loud:=detail);
    FormatNewformData(Sprintf("mfdata_%o.txt",B),Sprintf("mf_newforms_%o.txt",B),"polredabs_full.txt":Loud:=detail);
    FormatHeckeEigenvalueData(Sprintf("mfdata_%o.txt",B),Sprintf("mf_hecke_nf_%o.txt",B):Loud:=detail);
end procedure;

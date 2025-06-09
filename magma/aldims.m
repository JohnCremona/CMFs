// This file is for computing dimensions of AL spaces for a given sequence of Atkin-Lehner signs
// for the old and new spaces, and for the corresponding Eisenstein subspaces.

import "Caching.m" : SetCache, GetCache, class_nos, traces_coh, traces_eis, mu_star_mus, inv_weights;

// Since we are already constructing the space, we can do all the signs at once
// Here sgns are +-1, check later whether we prefer 0,1
function ALdimsModSym(N, k)
    assert k ge 2; // Modular symbols would not work for k=1
    Mk := ModularSymbols(N,k);
    Sk := CuspidalSubspace(Mk);
    Snew := NewSubspace(Sk);
    Sold := OldSubspace(Sk);
    Ek := EisensteinSubspace(Mk);
    // These two lines require suppressing a requirement in Magma's two intrinsics, to be added in future Magma version
    Enew := NewSubspace(Ek);
    Eold := OldSubspace(Ek);
    // We compute the redundant Ek, Sk and Mk for verification
    spaces := [Snew, Sold, Enew, Eold, Sk, Ek, Mk];
    keys := ["cusp_new", "cusp_old", "eis_new", "eis_old", "cusp", "eis", "full"];
    dims := AssociativeArray();
    for i->V in spaces do
        als := [AtkinLehnerOperator(V,p) : p in PrimeDivisors(N)];
        V_dims := [];
        for sgns in CartesianPower([1,-1],#als) do
            V_sgns := VectorSpace(Rationals(),Dimension(V));
            for j->s in sgns do
                V_sgns meet:= Kernel(als[j] - s);
            end for;
            Append(~V_dims, Dimension(V_sgns));
        end for;
        dims[keys[i]] := V_dims;
    end for;
    for i in [1..2^#PrimeDivisors(N)] do
        assert dims["cusp_new"][i] + dims["cusp_old"][i] eq dims["cusp"][i];
        assert dims["eis_new"][i] + dims["eis_old"][i] eq dims["eis"][i];
        assert dims["cusp"][i] + dims["eis"][i] eq dims["full"][i];
    end for;
    Remove(~dims, "cusp");
    Remove(~dims, "full");
    Remove(~dims, "eis");
    for key in ["cusp_new", "cusp_old"] do
        assert &and[IsEven(d) : d in dims[key]];
        dims[key] := [d div 2 : d in dims[key]];
    end for;
    return dims;
end function;

function ALdimsModSymTraces(N, k)
    assert k ge 2; // Modular symbols would not work for k=1
    Mk := ModularSymbols(N,k);
    Sk := CuspidalSubspace(Mk);
    Snew := NewSubspace(Sk);
    Sold := OldSubspace(Sk);
    Ek := EisensteinSubspace(Mk);
    // These two lines require suppressing a requirement in Magma's two intrinsics, to be added in future Magma version
    Enew := NewSubspace(Ek);
    Eold := OldSubspace(Ek);
    // We compute the redundant Ek, Sk and Mk for verification
    spaces := [Snew, Sold, Enew, Eold, Sk, Ek, Mk];
    keys := ["cusp_new", "cusp_old", "eis_new", "eis_old", "cusp", "eis", "full"];
    dims := AssociativeArray();
    for i->V in spaces do
        als := [AtkinLehnerOperator(V,p) : p in PrimeDivisors(N)];
        subsets := [ J : J in Subsets({1..#als})];
        if IsEmpty(als) then
            traces := [Dimension(V) : J in subsets];
        else
            traces := [Trace(&*[Universe(als) | als[j] : j in J]) : J in subsets];
        end if;
        V_dims := [Integers() | &+[&*[Integers() | sgns[j] : j in J]*traces[i] : i->J in subsets] / 2^(#als) 
                    : sgns in CartesianPower([1,-1],#als)];
        dims[keys[i]] := V_dims;
    end for;
    for i in [1..2^#PrimeDivisors(N)] do
        assert dims["cusp_new"][i] + dims["cusp_old"][i] eq dims["cusp"][i];
        assert dims["eis_new"][i] + dims["eis_old"][i] eq dims["eis"][i];
        assert dims["cusp"][i] + dims["eis"][i] eq dims["full"][i];
    end for;
    Remove(~dims, "cusp");
    Remove(~dims, "full");
    Remove(~dims, "eis");
    for key in ["cusp_new", "cusp_old"] do
        assert &and[IsEven(d) : d in dims[key]];
        dims[key] := [d div 2 : d in dims[key]];
    end for;
    return dims;
end function;

// For the trace formula, using [Assaf, a note on the trace formula]

function H(n)
// Returns the Kronecker-Hurwitz class number of n, as extended by Zagier, see [Popa, 2.2]
    if n lt 0 then
        is_sq, u := IsSquare(-n);
        return (is_sq select -u/2 else 0);
    end if;
    if n eq 0 then
        return -1/12;
    end if;
    if n mod 4 in [1,2] then
        return 0;
    end if;

    ret := 0;
    for d in Divisors(n) do
        if IsSquare(d) and  (n div d) mod 4 in [0,3] then
            b, v := GetCache(-n div d, class_nos);
            if not b then
                v := ClassNumber(-n div d);
                SetCache(-n div d, v, class_nos); 
            end if;
            ret +:= v;
        end if;
    end for;
    // ret := &+[ClassNumber(-n div d) : d in Divisors(n)
    // 		       | IsSquare(d) and (n div d) mod 4 in [0,3] ];
    if IsSquare(n) and IsEven(n) then
        ret -:= 1/2;
    end if;
    if n mod 3 eq 0 and IsSquare(n div 3) then
        ret -:= 2/3;
    end if;
    return ret;
end function;

// Gegenbauer polynomials
function P(k, t, m)
  R<x> := PowerSeriesRing(Rationals(), k-1);
  return Coefficient((1 - t*x+m*x^2)^(-1), k-2);
end function;

function Phil(N, l, a, d)
    l_prime := N div l;
    ret := 0;
    for r in Divisors(l_prime) do
	s := l_prime div r;
	g := GCD(r,s);
	if (((a-d) mod g eq 0) and (GCD(a,r) eq 1) and (GCD(d,s) eq 1)) then
	    ret +:= EulerPhi(g);
	end if;
    end for;
    return EulerPhi(l) * ret / l;
end function;

function Lemma4_5(N, u, D)
    assert N mod u eq 0;
    assert D mod (u^2) eq 0;
    ret := 1;
    fac := Factorization(N);
    for pa in fac do
	p, a := Explode(pa);
	i := Valuation(u, p);
	if (i eq 0) then continue; end if;
	b := Valuation(D, p);
	if IsOdd(p) then
	    if (i eq a) then ret *:= p^(Ceiling(a/2)); continue; end if;
	    if ((i le b-a) and IsEven(a-i)) then
		ret *:= (p^Ceiling(i/2) - p^(Ceiling(i/2)-1));
	    elif ((i eq b-a+1) and IsEven(a-i)) then
		ret *:= - p^(Ceiling(i/2)-1);
	    elif ((i eq b-a+1) and IsOdd(a-i)) then
		ret *:= p^Floor(i/2) * LegendreSymbol(D div p^b, p);
	    else
		return 0;
	    end if;
	else // p = 2
	    if (i eq a) then
		if (b ge 2*a+2) or ((b eq 2*a) and (((D div 2^b) mod 4) eq 1)) then 
		    ret *:= p^(Ceiling(a/2));
		elif (b eq 2*a+1) or ((b eq 2*a) and (((D div 2^b) mod 4) eq 3)) then
		    ret *:= -p^(Ceiling(a/2)-1);
		end if;
		continue;
	    end if;
	    if ((i le b-a-2) and IsEven(a-i)) then
		// print "case 1";
		ret *:= p^(Ceiling(i/2)-1);
	    elif ((i eq b-a-1) and IsEven(a-i)) then
		// print "case 2";
		ret *:= - p^(Ceiling(i/2)-1);
	    elif ((i eq b-a) and IsEven(a-i)) then
		// print "case 3";
		ret *:= p^(Ceiling(i/2)-1) * KroneckerCharacter(-4)(D div p^b);
	    elif ((i eq b-a+1) and IsOdd(a-i) and ((D div p^b) mod 4 eq 1) ) then
		// print "case 4";
		ret *:= p^Floor(i/2) * KroneckerSymbol(D div p^b, p);
	    else
		// print "returning 0";
		return 0;
	    end if;
	end if;
    end for;
    return ret;
end function;

function Sfast(N, u, t, n)
// Returns |S_N(u,t,n)| as defined in [Popa, 4.1]
// Recal S_N(u,t,n) = { \alpha in (Z/NZ)^{\times} : \alpha^2 - t \alpha + n = 0 (mod Nu)}
// It is called Sfast because it does not produce the set, buut merely counts using straight-forward formulas coming from 
// local-global principle and Hensel lifting.
    fac := Factorization(N*u);
    num_sols := 1;
    y := t^2-4*n;
    for f in fac do
        p,e := Explode(f);
        if (y eq 0) then
	        num_sols *:= p^(e div 2);
            continue;
        end if;
        e_y := Valuation(y, p);
        y_0 := y div p^e_y;
        // following [Assaf]
        if p eq 2 then
            if (e_y le e + 1) and IsOdd(e_y) then
                return 0;
            end if;
        if (e le e_y-2) then
            num_sols *:= 2^(e div 2);
        elif (e_y le e - 1) and IsEven(e_y) then
            num_sols *:= 2^(e_y div 2 - 1)*(1 + KroneckerSymbol(y_0, 2))*(1 + KroneckerSymbol(-1, y_0));
        elif (e eq e_y) and IsEven(e_y) then
            num_sols *:= 2^(e_y div 2 - 1)*(1 + KroneckerSymbol(-1, y_0));
        elif (e eq e_y - 1) and IsEven(e_y) then
            num_sols *:= 2^(e_y div 2 - 1);
        else
            Error("Not Implemented!");
        end if;
        else
            if e_y lt e then
                if IsOdd(e_y) then
                    return 0;
                end if;
                is_sq := IsSquare(Integers(p)!y_0);
                if not is_sq then
                    return 0;
                end if;
                num_sols *:= p^(e_y div 2) * 2;
            else
                num_sols *:= p^(e div 2);  
            end if;
        end if;
    end for;
    return Integers()!num_sols div u;
end function;

function Cfast(N, u, t, n)
// Returns C_N(u,t,n), computed using [Popa, Lemma 4.5]
    // S := [x : x in [0..N-1] | (GCD(x,N) eq 1) and (((x^2 - t*x + n) mod N) eq 0)];
    // nS1 := #S(N, 1, t, n);
    nS2 := Sfast(N, 1, t, n);
    // assert nS1 eq nS2;
    return nS2 * Lemma4_5(N, u, t^2 - 4*n);
end function;

function TraceFormulaALEis(N, k, Q)
    assert k ge 2;
    w := k - 2;
    S2 := 0;
    for d in Divisors(Q) do
        a := Q div d;
        if (a+d) mod Q eq 0 then
            // print "a = ", a, "d = ", d;
            S2 +:= Minimum(a,d)^(k-1)*Phil(N,Q,a,d) / Q^(w div 2);
            // print "S2 = ", S2;
        end if;
    end for;
     // Not sure - check
    if k eq 2 then
	    S2 -:= 1;
    end if;
    assert IsIntegral(S2);
    return Integers()!S2;
end function;

function TraceFormulaALCohomology(N, k, Q)
    S1 := 0;
    Q_prime := N div Q;
    assert GCD(Q, Q_prime) eq 1;
    w := k - 2;
    max_abst := Floor(SquareRoot(4*Q)) div Q;
    for tQ in [-max_abst..max_abst] do
        t := tQ*Q;
        for u in Divisors(Q) do
            for u_prime in Divisors(Q_prime) do
                if ((4*Q-t^2) mod (u*u_prime)^2 eq 0) then
                    // print "u =", u, " u_prime = ", u_prime, "t = ", t;
                    S1 +:= P(k,t,Q)*H((4*Q-t^2) div (u*u_prime)^2)*Cfast(Q_prime,u_prime,t,Q)*MoebiusMu(u) / Q^(w div 2);
                    // print "S1 = ", S1;
                end if;
            end for;
        end for;
    end for;
    // Not sure - check
    if k eq 2 then
	    S1 -:= 1;
    end if;
    assert IsIntegral(S1);
    return Integers()!S1;
    return S1;
end function;

// This formula follows Popa - On the Trace Formula for Hecke Operators on Congruence Subgroups, II
// Theorem 4. 
// (Also appears in Skoruppa-Zagier, but this way of stating the formula was easier to work with).
function TraceFormulaALCusp(N, k, Q)
    assert k ge 2;
    b, S1 := GetCache(<N,k,Q>, traces_coh);
    if not b then
        S1 := TraceFormulaALCohomology(N,k,Q);
        SetCache(<N,k,Q>, S1, traces_coh); 
    end if;
    // -S1 is trace on E + S + Sbar
    b, S2 := GetCache(<N,k,Q>, traces_eis);
    if not b then
        S2 := TraceFormulaALEis(N,k,Q);
        SetCache(<N,k,Q>, S2, traces_eis); 
    end if;
    // print "S2 = ", S2;
    ret := -S1 / 2 - S2 / 2;
    // this yields trace on S
    assert IsIntegral(ret);
    return Integers()!ret;
end function;

function TraceFormulaALFull(N, k, Q)
    assert k ge 2;
    S1 := TraceFormulaALCohomology(N,k,Q);
    // -S1 is trace on E + S + Sbar
    S2 := TraceFormulaALEis(N,k,Q);
    // print "S2 = ", S2;
    ret := -S1 / 2 + S2 / 2;
    // this yields trace on E + S
    assert IsIntegral(ret);
    return Integers()!ret;
end function;

function mu_star_mu(n)
    fac := Factorization(n);
    ret := 1;
    for pa in fac do
        p,a := Explode(pa);
        if a ge 3 then return 0; end if;
        if a eq 1 then ret *:= (-2); end if;
    end for;
    return ret;
end function;

function weights_of_traces(d, Q)
    g := GCD(d,Q);
    is_sq := IsSquare(g);
    if not is_sq then return 0; end if;
    return #Divisors(d div g);
end function;

function inverse_weights_of_traces(d, Q)
    g := GCD(d, Q);
    is_sq, m := IsSquare(g);
    if not is_sq then return 0; end if;
    dog := d div g;
    b, msm := GetCache(dog, mu_star_mus);
    if not b then
        msm := mu_star_mu(dog);
        SetCache(dog, msm, mu_star_mus); 
    end if;
    msm := mu_star_mu(d div g);
    return MoebiusMu(m) * msm;
end function;

function TraceFormulaALNew(N, k, Q, orig_trace)
    wts := [];
    for Nprime in Divisors(N) do
        NoNp := N div Nprime;
        b, wt := GetCache(<NoNp, Q>, inv_weights);
        if not b then
            wt := inverse_weights_of_traces(NoNp, Q);
            SetCache(<NoNp, Q>, wt, inv_weights); 
        end if;
        Append(~wts, wt);
    end for;
    trace := &+[orig_trace(Nprime, k, GCD(Q, Nprime))*wts[j] : j->Nprime in Divisors(N)];
    return trace;
end function;

// When k = 2, we separate the Eisenstein series to two spaces
// Eis_2(N) = Eis_2(N)^(not-1) + Eis_2(N)^(1)
// where the Eis_2(N)^(1) are spanned by alpha_1(E_2(N)) - alpha_d(E_2(N)) for d | N
// Then the not-1 space has a direct sum decomposition in terms of
// the new subspaces as before, but the 1-space has the following traces - 
// Tr(W_Q | Eis_2(N)^(1)) = -1 if Q is not a square
// and Tr(W_Q | Eis_2(N)^(1)) = sigma_0(N/Q)-1 if Q is a square
// The Eis_2(N)^(1) contributes to the new subspace iff N is prime

function TraceFormulaALEisOne(Q,N)
    if N eq 1 then return 0; end if;
    if Q eq 1 then return #Divisors(N) - 1; end if;
    if not IsSquare(Q) then return -1; end if;
    return #Divisors(N div Q) - 1;
end function;

// This is actually not true, as Eisenstein series do not satisfy the same 
// direct sum decomposition
function TraceFormulaALEisNew(N,k,Q)
    function trace_formula(N,k,Q)
        trace := TraceFormulaALEis(N,k,Q);
        if (k eq 2) then
            trace -:= TraceFormulaALEisOne(Q,N);
        end if;
        return trace;
    end function;
    trace := TraceFormulaALNew(N, k, Q, trace_formula);
    if (k eq 2) and IsPrime(N) then
        if Q eq N then trace -:= 1; end if;
        if Q eq 1 then trace +:= 1; end if;
    end if;
    return trace;
end function;

function TraceFormulaALCuspNew(N,k,Q)
    return TraceFormulaALNew(N, k, Q, TraceFormulaALCusp);
end function;

// This is actually not true for k = 2, as Eisenstein series do not satisfy the same 
// direct sum decomposition because of the trivial character. 
function TraceFormulaALFullNew(N,k,Q)
    return TraceFormulaALNew(N, k, Q, TraceFormulaALFull);
end function;

function TraceFormulaALEisOld(N,k,Q)
    return TraceFormulaALEis(N,k,Q) - TraceFormulaALEisNew(N, k, Q);
end function;

function TraceFormulaALCuspOld(N,k,Q)
    return TraceFormulaALCusp(N,k,Q) - TraceFormulaALCuspNew(N, k, Q);
end function;

function ALdimsTraceFormula(N, k : Debug := false)
    keys := ["cusp_new", "cusp_old", "eis_new", "eis_old"];
    trace_formulas := [TraceFormulaALCuspNew, TraceFormulaALCuspOld, TraceFormulaALEisNew, 
                            TraceFormulaALEisOld];
    if Debug then
        assert k ge 2; // Trace formula would not work for k=1
        // We compute the redundant Ek, Sk and Mk for verification
        keys cat:= ["cusp", "eis", "full"];
        trace_formulas cat:= [TraceFormulaALCusp, TraceFormulaALEis, TraceFormulaALFull];
    end if;
    dims := AssociativeArray();
    als := [p^Valuation(N,p) : p in PrimeDivisors(N)];
    for i->V in keys do
        subsets := [ J : J in Subsets({1..#als})];
        Qs := [&*[Integers() | als[j] : j in J] : J in subsets];
        traces := [trace_formulas[i](N,k,Q) : Q in Qs];
        V_dims := [Integers() | &+[&*[Integers() | sgns[j] : j in J]*traces[i] : i->J in subsets] / 2^(#als) 
                    : sgns in CartesianPower([1,-1],#als)];
        dims[keys[i]] := V_dims;
    end for;
    if Debug then
        for i in [1..2^#PrimeDivisors(N)] do
            assert dims["cusp_new"][i] + dims["cusp_old"][i] eq dims["cusp"][i];
            assert dims["eis_new"][i] + dims["eis_old"][i] eq dims["eis"][i];
            assert dims["cusp"][i] + dims["eis"][i] eq dims["full"][i];
        end for;
        Remove(~dims, "cusp");
        Remove(~dims, "full");
        Remove(~dims, "eis");
    end if;
    return dims;
end function;

function TraceALonMS(N, k, Q : New := false, Sub := "Cusp")
    MS := ModularSymbols(N,k);
    MSnew := MS;
    if New then
        MSnew := NewSubspace(MS);
    end if; 
    if Sub eq "Cusp" then
        S := CuspidalSubspace(MSnew);
    elif Sub eq "Eis" then
        S := EisensteinSubspace(MSnew);
    else    
        assert false;
    end if;
    w := AtkinLehner(MS,Q);
    BS := BasisMatrix(VectorSpace(S));
    trace := Trace(Solution(BS*w, BS));
    assert IsIntegral(trace);
    trace := Integers()!trace;
    if Sub eq "Cusp" then
        assert IsEven(trace);
        trace div:= 2;
    end if;
    return trace;
end function;

procedure test_ALdims(N,k)
    aldims_modsym := ALdimsModSym(N,k);
    aldims_modsym_traces := ALdimsModSymTraces(N,k);
    aldims_traces := ALdimsTraceFormula(N,k);
    assert &and[aldims_modsym[k] eq aldims_modsym_traces[k] : k in Keys(aldims_modsym)];
    assert &and[aldims_modsym[k] eq aldims_traces[k] : k in Keys(aldims_modsym)];
end procedure;

procedure test_many_ALdims(: Ns := [1..100], ks := [2..8 by 2])
    for N in Ns do
        for k in ks do
            print N,k;
            test_ALdims(N,k);
        end for;
    end for;
end procedure;

procedure write_line(keys, N, k, fp)
    al_dims := ALdimsTraceFormula(N,k);
    data := [al_dims[key] : key in keys];
    data_str := Sprintf("%o:%o:", N, k) cat Join([Sprintf("%o", x) : x in data], ":");
    Puts(fp, data_str);
    return;
end procedure;

// write all data for N up to N_max and k up to k_max
procedure write_ALdims_upto(N_max,k_max : OnlyPrimes := false)
    fname := Sprintf("mf_aldims_N_%o_k_%o.m.txt",N_max, k_max);
    keys := ["cusp_new", "cusp_old", "eis_new", "eis_old"];
    SetColumns(0);
    fp := Open(fname, "w");
    Ns := OnlyPrimes select PrimesUpTo(N_max) else [1..N_max];
    for N in Ns do
        for k in [2..k_max by 2] do
            write_line(keys, N, k, fp);
        end for;
    end for;
    delete fp;
    return;
end procedure;

// write all data for N k^2 up to Nk2 
procedure write_ALdims_Nk2_upto(Nk2_min, Nk2_max : N_min := 1, N_max := Nk2_max div 4)
    fname := Sprintf("mf_aldims_Nk2_%o_%o_N_%o_%o.m.txt",Nk2_min,Nk2_max,N_min,N_max);
    keys := ["cusp_new", "cusp_old", "eis_new", "eis_old"];
    SetColumns(0);
    fp := Open(fname, "w");
    for N in [N_min..N_max] do
        k_min := 2*Ceiling(Sqrt(Nk2_min/N)/2);
        k_max := 2*Floor(Sqrt(Nk2_max/N)/2);
        for k in [k_min..k_max by 2] do
            write_line(keys, N, k, fp);
        end for;
    end for;
    delete fp;
    return;
end procedure;

// Following completeness pages on the LMFDB
// 1. This covers the cases of Nk^2 <= 4000, chi trivial and Nk^2 <= 40000, N <= 24 and Nk^2 <= 40000, k > 1, dim S_k(N,chi)^new <= 100 and Nk^2 <= 40000
// This one takes several minutes on a single machine
// write_ALdims_Nk2_upto(40000);

// 2. This covers N <= 10, Nk^2 <= 100000
// How long is this one?
// write_ALdims_Nk2_upto(100000 : N_max := 10);

// 3. This covers the case N <= 100, k <= 12
// This one is really quick
// write_ALdims_upto(100,12);

// 4. k = 2, chi trivial N <= 50000
// This one takes several minutes
// write_ALdims_upto(50000, 2);

// 5. k = 2, chi trivial, N <= 10^6 prime
// This one is long. How long? 
// write_AL_dims_upto(10^6, 2 : OnlyPrimes);

// if assigned exitsignal and eval(exitsignal) then exit; end if;
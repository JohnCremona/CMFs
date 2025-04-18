// This file is for computing dimensions of AL spaces for a given sequence of Atkin-Lehner signs
// for the old and new spaces, and for the corresponding Eisenstein subspaces.

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
        traces := [Trace(&*[Universe(als) | als[j] : j in J]) : J in subsets];
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

// For the trcae formula, using [Assaf, a note on the trace formula]

function H(n)
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

  ret := &+[ClassNumber(-n div d) : d in Divisors(n)
		       | IsSquare(d) and (n div d) mod 4 in [0,3] ];
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

// This can be made faster - look at the Shimura curve code
function Cfast(N, u, t, n)
    S := [x : x in [0..N-1] | (GCD(x,N) eq 1) and (((x^2 - t*x + n) mod N) eq 0)];
    return #S * Lemma4_5(N, u, t^2 - 4*n);
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
    S1 := TraceFormulaALCohomology(N,k,Q);
    // -S1 is trace on E + S + Sbar
    S2 := TraceFormulaALEis(N,k,Q);
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
    return MoebiusMu(m) * mu_star_mu(d div g);
end function;

function TraceFormulaALNew(N, k, Q, orig_trace)
    trace := &+[orig_trace(Nprime, k, GCD(Q, Nprime))*inverse_weights_of_traces(N div Nprime, Q) : Nprime in Divisors(N)];
    return trace;
end function;

// This is actually not true, as Eisenstein series do not satisfy the same 
// direct sum decomposition
function TraceFormulaALEisNew(N,k,Q)
    return TraceFormulaALNew(N, k, Q, TraceFormulaALEis);
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

function ALdimsTraceFormula(N, k)
    assert k ge 2; // Trace formula would not work for k=1
    // We compute the redundant Ek, Sk and Mk for verification
    keys := ["cusp_new", "cusp_old", "eis_new", "eis_old", "cusp", "eis", "full"];
    trace_formulas := [TraceFormulaALCuspNew, TraceFormulaALCuspOld, TraceFormulaALEisNew, 
                        TraceFormulaALEisOld, TraceFormulaALCusp, TraceFormulaALEis, TraceFormulaALFull];
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
    for i in [1..2^#PrimeDivisors(N)] do
        assert dims["cusp_new"][i] + dims["cusp_old"][i] eq dims["cusp"][i];
        assert dims["eis_new"][i] + dims["eis_old"][i] eq dims["eis"][i];
        assert dims["cusp"][i] + dims["eis"][i] eq dims["full"][i];
    end for;
    Remove(~dims, "cusp");
    Remove(~dims, "full");
    Remove(~dims, "eis");
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
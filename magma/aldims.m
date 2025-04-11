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
        V_dims := [Integers() | &+[&*[Integers() | sgns[j] : j in J]*Trace(&*[Universe(als) | als[j] : j in J]) : J in Subsets({1..#als})] / 2^(#als) 
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
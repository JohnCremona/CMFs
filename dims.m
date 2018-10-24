Attach("chars.m");
function Newspace(N,k,o)
  G, T := CharacterOrbitReps(N:RepTable);
  chi:=G[o];
  Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1)));
chi_deg := EulerPhi(Order(chi));
rel_deg := Dimension(Snew);
dim := chi_deg*rel_deg;
printf "dim(%o:%o:%o) = %o*%o = %o\n", N, k, o, chi_deg, rel_deg, dim;
return Snew;
end function;

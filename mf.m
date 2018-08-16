function DirichletCharacterGaloisReps(N)
  G := [chi:chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N))];
  T := Sort([<[Trace(u):u in ValueList(G[i])],i>:i in [1..#G]]);
  return Reverse([G[T[i][2]]:i in [1..#G]]);
end function;

function NewspaceDecomposition (chi, k)
    return [Dimension(S)*EulerPhi(Order(chi)):S in NewformDecomposition(NewSubspace(CuspidalSubspace(ModularSymbols(chi,k,-1))))];
end function;

function NewspaceDimension (chi, k)
    return Dimension(NewSubspace(CuspidalSubspace(ModularForms(chi,k))));
end function;

function sum(X) return #X eq 0 select 0 else &+X; end function;

procedure DecomposeSpaces(filename,minN,maxN,mink,maxk)
    assert minN gt 0 and maxN ge minN;
    assert mink gt 1 and maxk ge mink;
    fp := Open(filename,"w");
    for N:=minN to maxN do
        G:=DirichletCharacterGaloisReps(N);
        for k:=mink to maxk do
            for i in [1..#G] do
                start := Cputime();
                X:=NewspaceDecomposition(G[i],k);
                t := Cputime()-start;
                str:=StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o",N,k,i,t,X));
                Puts(fp,str);
                Flush(fp);
            end for;
        end for;
    end for;
end procedure;

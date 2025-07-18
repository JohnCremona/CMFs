/*
First select galois-orbit rep for source by doing:

   cat alltwists.txt_* | awk -F. '{if (substr($6,1,2)=="1:") print $R}'  >alltwistreps.txt

in bash, and then in magma:

   Attach("utils.m");
   S := getrecs("conrey_10000.txt");
   X := {[r[1],StringToStrings(r[3])[1]]:r in S};
   S := getrecs("alltwistreps.txt");
   S := [r:r in S| [s[1],s[5]] in X where s:=Split(r[1],".")];
   putrecs("alltwistreps.txt",S);

Usage is then

   magma -b infile:=alltwistreps.txt outfile:=galtwists.txt twistgalois.m

output is source:target:[psi1,...,psin]:[m1,...mn]:[Ds] where source and targer are newform orbit labels, psi1,...psin are char orbit labels,
and m1,...,mn are multiplicities where mj counts the number of distinct characters in the character orbit psij that map any fixedq embedded newform in source
to some embedded newform in target.  The last columns Ds is a list of RM/CM discriminants for self-twists (only relevant when source=target)
*/

Attach("utils.m");
Attach("mfutils.m");
Attach("chars.m");

time S := getrecs (infile);
fp := Open(outfile,"w");  
time X := IndexFibers (S, func<r|[SplitNewformLabel(Join(Split(r[1],".")[1..4],".")),SplitNewformLabel(Join(Split(r[2],".")[1..4],"."))]>);
time T := ConreyOrbitTable ("conrey_10000.txt",10000);
time pairs := Sort([x:x in Keys(X)]);
t := Cputime();
cnt := 0; prevcnt := 0;
for x in pairs do
    C := &cat[StringToStrings(r[3]):r in X[x]];
    C := [[atoi(s[1]),atoi(s[2])] where s:=Split(c,"."):c in C];
    C := Multiset([[z[1],T[z[1]][z[2]]]:z in C]);
    Cx := Sort([c:c in Set(C)]);  Cm := [Multiplicity(C,c):c in Cx];
    st := x[1] eq x[2] select [r:r in X[x]|r[1] eq r[2]] else [];
    if #st gt 0 then
        assert #st eq 1;  st := st[1];
        st := [[atoi(s[1]),atoi(s[2])] where s:= Split(c,"."):c in StringToStrings(st[3])];
        assert st[1] eq [1,1];
        st := [Parity(s[1],s[2])*s[1]: s in st[2..#st]];
        st := Sort([(D mod 4) in [0,1] select D else 4*D : D in st],func<a,b|Abs(a)-Abs(b)>);
    end if;
    Cx := [CharacterOrbitLabel(c[1],c[2]):c in Cx];
    Puts(fp,Join([NewformLabel(x[1][1],x[1][2],x[1][3],x[1][4]),NewformLabel(x[2][1],x[2][2],x[2][3],x[2][4]),sprint(Cx),sprint(Cm),sprint(st)],":"));  cnt +:= 1;
    if cnt-prevcnt ge 10000 then Flush(fp); printf "Wrote %o records to output file %o\n", cnt, outfile; prevcnt:=cnt; end if;
end for;
printf "Wrote %o twist records to %o in %.3os\n", cnt, outfile, Cputime()-t;
exit;


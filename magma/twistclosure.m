Attach("utils.m");
Attach("chars.m");
Attach("mfutils.m");

infile := Sprintf("mintwists.txt_%o", k); // format is source:target:[psi1,..psin] where source and target are embedded newform labels,
                                          // with source the designated twist-class representative, and the psi's are Conrey labels
outfile := Sprintf("alltwists.txt_%o",k);

cmp := func<a,b|(c ne 0 select c else CompareEmbeddedNewformLabels(a[2],b[2])) where c:=CompareEmbeddedNewformLabels(a[1],b[1])>;
function closure(S) // S should be a list of twists of the same newform (the designated representative of its twist class
    L := [<r[1],r[2],[[StringToInteger(s[1]),StringToInteger(s[2])] where s:=Split(x,"."):x in StringToStrings(r[3])]>:r in S];
    LL := [<r[2],s[2],Sort([z:z in Set([[q,n] where
                            q,n:=AssociatedPrimitiveCharacter(qq,nn) where qq,nn:=
                            ConreyCharacterProduct(x[1],ConreyInverse(x[1],x[2]),y[1],y[2]):x in r[3],y in s[3]])])>:r,s in L];
    return Sort([[r[1],r[2],sprint([Sprintf("%o.%o",x[1],x[2]):x in r[3]])]:r in LL],cmp);
end function;

time S := getrecs(infile);
time X := IndexFibers(S,func<r|SplitEmbeddedNewformLabel(r[1])>);
t := Cputime();
fp := Open(outfile,"w");  cnt := 0;  prevcnt:=0;
for x in Sort([x:x in Keys(X)]) do
    T := closure(X[x]);
    for r in T do Puts(fp,Join(r,":")); end for;
    cnt +:= #T;
    if cnt-prevcnt ge 10000 then printf "Wrote %o twists to output file %o (%.3o)\n", cnt-prevcnt, outfile, Cputime()-t; prevcnt := cnt; Flush(fp); end if;
end for;
delete fp;
printf "Computed a total of %o twists in %.3os\n", cnt, Cputime()-t;
exit;

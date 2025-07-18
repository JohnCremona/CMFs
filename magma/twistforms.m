Attach("utils.m");
Attach("chars.m");
Attach("mfutils.m");

RR:=RealField(20);
CC<i>:=ComplexField(RR);
SetDefaultRealField(RR);
twistcharfile := Sprintf("twistchars_10000_relevant.txt_%o",k); // format is chi:psi:tchi where chi,psi,tchi are conrey labels q.n
mfheckeccfile := Sprintf("mf_hecke_cc_an_100.txt_%o",k);        // format is label:an where label is an embedded newform label and an is a list of pairs of reals
outfile := Sprintf("mintwists.txt_%o",k);                       // format is source:target:[psi1,...,psin] where source/target are embedded newform labels N.k.a.x.n.i
                                                                // with source the twist class representative of target, and psi1,,,psin are Conrey labels

s := Cputime();
S := getrecs(twistcharfile);
X := IndexFibers(S,func<r|r[1]>);   // index by Conrey label N.n
t := Cputime(); printf "Loaded %o twisting character records from %o (%.3os)\n", #S, twistcharfile, t-s; s := t;
time S := getrecs(mfheckeccfile);
if #S eq 0 then printf "No newforms of weight %o to process, wrote 0 records to output file %o\n", k, outputfile; fp := Open(outputfile,"w"); delete fp; exit; end if;
time Z := Sort([Append(SplitEmbeddedNewformLabel(S[j][1]),j):j in [1..#S]]);
n := #atofff(S[1][2]); P := PrimesInInterval(1,n);  // don't assume n=100, we use more coeffs for k=1
function strtoap(s) return [CC![StringToReal(y[1..n-1]),StringToReal(y[n+1..Index(y,"]")-1])] where n:=Index(y,",") : y in Split(s[2..#s-1],"[")[P]]; end function; // leave normalized
function distance(ap,bp,N) return &+[Norm(ap[i]-bp[i]):i in [1..#ap]|N mod P[i] ne 0]; end function;
time S := [<r[1],strtoap(r[2])> where r:=S[Z[i][7]]:i in [1..#S]];
I := [i:i in [1..#S]];
time F := IndexFibers(I,func<i|Join([a[1],a[2],a[5]],".") where a:=Split(S[i][1],".")>);    // index by embedded newspace label N.k.n
t := Cputime(); printf "Loaded %o weight-%o embedded newforms in %o embedded newspaces from file %o (%.3os)\n", #S, k, #F, twistcharfile, t-s; s := t;
T := AssociativeArray();

prevlabel := "";

for r in S do
    if IsDefined(T,r[1]) then continue; end if;
    label := r[1];
    a := Split(label,".");
    if a[2] ne k then continue; end if;
    assert prevlabel eq "" or CompareEmbeddedNewformLabels(label,prevlabel) gt 0;
    chi := Join([a[1],a[5]],".");
    // chi might not be minimal, it could be a twist of a minimal character of the same modulus that comes later in our ordering by char orbit label
    if not IsMinimal(chi) then continue; end if;    // We will check that this newform gets hit at the end
    printf "%o is the designated representative of its twist class\n", label;
    T[label] := [label,"1.1"];  // This form is officially the minimal representative of its twist class
    if not IsDefined(X,chi) then continue; end if;  // This will happen if there are no non-trivial twists in the database
    twists := [x : x in X[chi]];
    // printf "Twisting embedded newform %o by %o characters\n", r[1], #twists;
    for x in twists do
        psi := ComplexConreyCharacter(x[2],CC);
        cpsi := atoi(Split(x[2],".")[1]);
        tspace := b[1] cat "." cat a[2] cat "." cat b[2] where b := Split(x[3],".");
        assert IsDefined(F,tspace);
        ap := [psi(P[i])*r[2][i]:i in [1..#P]];
        ds := [distance(ap,S[i][2],cpsi): i in F[tspace]];
        v,m := Min(ds);  if v ge 0.000001 then print label,x,ds; assert v lt 0.000001; end if;
        if #ds gt 1 then v := Min([ds[i]:i in [1..#ds]|i ne m]); if v le 1.0 then print label,x,ds; assert v gt 1.0; end if; end if;
        twistlabel := S[F[tspace][m]][1];
        printf "Twist of %o by %o is %o\n", label, x[2], twistlabel;
        if IsDefined(T,twistlabel) then assert T[twistlabel][1] eq label; T[twistlabel] := Append(T[twistlabel],x[2]); else T[twistlabel] := [label,x[2]]; end if;
    end for;
end for;
assert #T eq #S;    // this will fail if we did not hit a newform of non-minimal chracter with a twist of a minimal character twist-class representative
print "Succesfully computed all twists, sorting into twist classes...";
cmp := func<a,b|(c ne 0 select c else CompareEmbeddedNewformLabels(a[2],b[2])) where c:=CompareEmbeddedNewformLabels(a[1],b[1])>;
time X := Sort([[T[r[1]][1],r[1],sprint(T[r[1]][2..#T[r[1]]])]:r in S],cmp);
putrecs(outfile,X);
printf "Wrote %o records to output file %o (%.3os)\n", #S, outputfile, Cputime()-s;
exit;

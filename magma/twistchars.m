jobs := assigned Jobs select atoi(Jobs) else 1;
assert jobs gt 0;
jobid := assigned JobId select atoi(JobId) mod jobs else 0;

Attach("chars.m");

function pConductor(p,e,n1,n2)
    R := Integers(p^e); n := (R!n1)*(R!n2);
    if n eq 1 then return 1; end if;
    c := p^(Valuation(Order(n),p)+1);
    return p eq 2 and e gt 2 and ConreyCharacterValue(2^e,Integers()!n,5) ne 1 select 2*c else c;
end function;

B := 2000; conreyfile := "conrey_4000.txt";
start := Cputime();
cnt0:= 0; cnt1:=0; cnt2:=0;
L := [[m:m in [1..B]|m gt 1 and Valuation(m,2) ne 1 and LCM(n,m*ConductorProductBound(m,n))le B]:n in [1..B]];
L := [[<m,pps,LCM(m,n) div &*[Integers()|r[1]^r[2]:r in pps]> where pps:=[[p,Valuation(n,p)]:p in PrimeDivisors(n)|Valuation(m,p) eq Valuation(n,p)]:m in L[n]]:n in [1..B]];
s := Cputime();
S := [r:r in getrecs(conreyfile)|atoi(r[1]) le B];
t := Cputime(); printf "%o character orbits of modulus <= %o found in %o (%.3os)\n", #S, B, conreyfile, t-s;  s := t;
Mchi := &cat[[[q,n]:n in atoii(r[3])] where q:=atoi(r[1]) : r in S | r[10] eq "1"];
t := Cputime(); printf "%o minimal characters of modulus <= %o (%.3os)\n", #Mchi, B, t-s;  s := t;
Pchi := &cat[[[q,n]:n in atoii(r[3])] where q:=atoi(r[1]) : r in S|r[1] eq r[4] and r[1] ne "1"];
t := Cputime(); printf "%o nontrivial primitive characters of modulus <= %o (%.3os)\n", #Pchi, B, t-s;  s := t;
X := IndexFibers(Pchi,func<r|r[1]>);
t := Cputime(); printf "Indexed %o primitive characters by modulus <= %o (%.3os)\n", #Pchi, B, t-s;  s:=t;
filename := jobs gt 1 select Sprintf("twistchars_%o_%o.txt", B, jobid) else Sprintf("twistchars_%o.txt");
fp := Open(filename,"w");
cnt := 0;
for chi in Mchi do
    cnt +:= 1;
    if cnt mod jobs ne jobid then continue; end if;
    cnt0 +:= 1;
    pchi := [q,n] where q,n := AssociatedPrimitiveCharacter (chi[1],chi[2]);
    for r in L[pchi[1]] do
        psiq := r[1];  pps := r[2];  d:= r[3];
        cnt1 +:= #X[psiq];
        for psi in X[psiq] do
            c := d * &*[Integers()|pConductor(pp[1],pp[2],pchi[2],psi[2]) : pp in pps];
            // assert c eq PrimitiveConductorProduct(pchi[1],pchi[2],psi[1],psi[2]);
            N := LCM(chi[1],psi[1]*c);
            if N le B then
                cnt2 +:= 1;
                q,n := Twist(chi[1],chi[2],psi[1],psi[2]);
                assert q eq N;
                Puts(fp,Sprintf("%o.%o:%o.%o:%o.%o",chi[1],chi[2],psi[1],psi[2],q,n));
            end if;
        end for;
    end for;
    Flush(fp);
end for;
Flush(fp);
t := Cputime(); printf "Computed %o twists, output written to %o (%.3os)\n", cnt2, filename, t-s;
if jobs gt 1 then
printf "Job %o (of %o) processed a total of %o pairs, considering %o, finding %o twists of modulus <= %o (%.3os)\n", jobid, jobs, cnt0*#Pchi, cnt1, cnt2, B, Cputime()-start;
else
printf "Processed a total of %o pairs, considering %o, finding %o twists of modulus <= %o (%.3os)\n", cnt0*#Pchi, cnt1, cnt2, B, Cputime()-start;
end if;
delete fp;
exit;

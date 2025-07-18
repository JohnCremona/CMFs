load "wt1artin.m";
t := Cputime();
L := [r[5]:r in getrecs("wt1_artin_match_4000.txt")|r[11] eq f];
F := LoadWeightOneForm("mfdata_wt1_4000.txt",L);
printf "Loaded %o weight one forms in %.1os\n", #L, Cputime()-t;
for i,j in [1..#F] do
    t := Cputime();
    printf "Searching for twists %o -> %o\n", F[i]`label, F[j]`label;
    psis,cnts := IsTwist(F[j]`an,F[j]`chi,F[i]`an,F[i]`chi:AllTwists,Verbose);
    printf "%o:%o:%o:%o:%.1os\n",F[i]`label,F[j]`label,sprint(psis),sprint(cnts),Cputime()-t;
    assert #psis gt 0;
end for;
exit;

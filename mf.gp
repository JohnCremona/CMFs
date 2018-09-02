\\  Function to sort Dirichlet characters according to Drew's system, as
\\ implemented in the Magma function DirichletCharacterGaloisReps(N)

character_traces(N, G, chi) =
{
        \\ G[1] is the order, phi(N) and G[2] is the list
        \\ of elementary divisors of (Z/NZ)^*, with the gp convention of
        \\ the largest first, so G[2][1] is the exponent:
        d = G[2][1];
        z = Mod(x, polcyclo(d));
        v = vector(N,j,trace(chareval(G,chi,j-1,[z,d])));
        return(v);
}

oldDirichletCharacterGaloisReps(N) =
{
        ZNstar = znstar(N,1);
        phiN = ZNstar[1];
        Chars = chargalois(ZNstar);
        nChars = length(Chars);
        \\  vecsort gives the opposite order to the one we want so we reverse
        vv = Vecrev(vecsort(vector(nChars, i,  [character_traces(N,ZNstar,Chars[i]), i] )));
        sChars = vector(nChars, i, Chars[vv[i][2]]);
        return(sChars);
}

DirichletCharacterGaloisReps(N) =
{
        ZNstar = znstar(N,1);
        phiN = ZNstar[1];
        Chars = chargalois(ZNstar);
        nChars = length(Chars);
        vv = vecsort(vector(nChars, i,  [concat([charorder(ZNstar,Chars[i])],character_traces(N,ZNstar,Chars[i])), i] ));
        sChars = vector(nChars, i, Chars[vv[i][2]]);
        return(sChars);
}

VecFind(v,a) =
{
  for(i=1,#v,if(a==v[i],return(i)));
  return(0);
}

DirCharPerm(N) =
{
  old = oldDirichletCharacterGaloisReps(N);
  new = DirichletCharacterGaloisReps(N);
  return(vector(#new,i,VecFind(old,new[i])));
}

\\ The next function is adapted from Karim's dims():

NewspaceDecomposition (N,G,chi, k) =
{
  cd = eulerphi(charorder(G,chi));
  Snew = mfinit([N, k, [G,chi]], 0);
  if (!mfdim(Snew), return([]));
  pols = mfsplit(Snew,,1)[2];
  \\print(pols);
  return ([cd*poldegree(P) | P<-pols]);
}

polytype(f) =
{
 for(i=0,poldegree(f),
          c=polcoeff(f,i);
          if(type(c)=="t_POLMOD",return(c.mod)));
 return("Q");
}

polredbest_stable(f) =
\\ repeat polred best until no change
{
  oldf = 0;
  while(f!=oldf, oldf=f; f=polredbest(f));
  return(f);
}

Absolutise(G, chi, f, flag=0) =
{
 my(ord,field,pol);
 ord = charorder(G,chi);
 field = polytype(f);
 if(field=="Q", if(ord<=2, pol=f, Qchi=nfinit(polcyclo(ord,xx));pol=rnfequation(Qchi,f)),
                Qchi=nfinit(field);pol=rnfequation(Qchi,f));
 pol=polredbest_stable(pol);
 if(flag,pol=polredabs(pol));
 return(pol);
}

NewspaceDecompositionWithPolys (N,G,chi, k, dmax) =
{
  my(cd,Snew,pols,dims,polys);
  cd = eulerphi(charorder(G,chi));
  Snew = mfinit([N, k, [G,chi]], 0);
  if (!mfdim(Snew), return([]));
  pols = mfsplit(Snew,,1)[2];
  \\print(pols);
  dims = [cd*poldegree(P) | P<-pols];
  polys = [Vecrev(Absolutise(G,chi,P)) | P<-pols, cd*poldegree(P)<=dmax];
  return ([dims,polys]);
}

abstrace(x, deg) =
\\ trace of a t_POLMOD does what is expected but trace of an int
\\ doubles it.  Also we might see an int as one coefficient of a newform
\\ most of whose coefficients are t_POLMODs.  In this case we need to
\\ multiply by the appropriate degree, so have to pass the degree as a
\\ parameter.

{
  my(y);
  \\printf("Taking absolute trace of %s (type %s) in degree %d\n",x,type(s),deg);
  if(type(x)=="t_INT" || deg==1,return(deg*x));
  y=trace(x);
  if(type(y)=="t_POLMOD",y=trace(y));
  \\printf("--returning %d\n",y);
  return(y);
}

\\ change variable of a polmod from x to y
changevar(a,x,y) =
{
  if(type(a)!="t_POLMOD",return(a),
                         return(Mod(subst(lift(a),x,y),subst(a.mod,x,y))));
}

/* convert a polmod/polmod representing an element of a relative
extension to a single list of coefficients with respect to a bi-power
basis.  For example (quadratic over quartic),

Mod(Mod(1, t^4 + t^3 + t^2 + t + 1), y^2 + Mod(-t - 1, t^4 + t^3 + t^2 + t + 1)*y + Mod(t^2 + 3*t + 1, t^4 + t^3 + t^2 + t + 1))

is a poly of degree 2 in y with (reversed) coefficients 1, -t-1, t^2+3*t+1  (modulo a quartic in t) so becomes

[t^2+3*t+1, -t-1, 1] --> [[0,3,1,0],[-1,-1,0,0],[1,0,0,0]] --> [0,3,1,0,-1,-1,0,0,1,0,0,0]

where the coefficient list gives the coefficients of y^i*t^j with
(i,j) in lexicographical order (0,0),(0,1),(0,2),(0,3),(1,0),...

Note that we want the output to have a fixed length 

*/

bipower_coeffs(a) =
{
 my(dtop = poldegree(a.mod), L);
 L = Vec(lift(a),dtop);
 for(i=1,dtop,if(type(L[i])=="t_POLMOD",dbot = poldegree(L[i].mod);break));
 for(i=1,dtop,if(type(L[i])=="t_POLMOD",L[i]=Vec(lift(L[i]),dbot),c=L[i];L[i]=vector(dbot,j,0);L[i][1]=c));
 concat(L);
}

change_basis(an,M,newpol) =
\\ Here the double Vecrev is because our matrices M are indexed from 0 to deg-1,
\\ while gp's Vec() and Pol() functions start with the leading coefficient.
{
  my(d = poldegree(newpol));
  Mod( Pol(Vecrev(Vecrev(lift(an),d)*M)), newpol);
}

change_basis_vec(anvec,oldpol,newpol) =
{
  my(d,alpha,M);
  if(oldpol==newpol, return(anvec));
  d = poldegree(oldpol);
  alpha = Mod(nfisisom(oldpol,newpol)[1],newpol);
  M = vector(d,i,Vecrev(lift(alpha^i),d));
  M = matrix(#M,#M[1],i,j,M[i][j]);
  for(j=1,#anvec,anvec[j] = change_basis(anvec[j],M,newpol));
  anvec;
}

absolutize_vec(anvec,botpol,toppol,abspol) =
{
  my(zet,t,y,pol,pol1,gam);
  \\ (1) embed small field into large field K: zeta is the image of the generator
  zet = Mod(nfisincl(botpol,abspol)[1], abspol);
  \\ (2) find a root of toppol in K
  t = variable(botpol);
  y = variable(toppol);
  \\print(toppol, " of type ", type(toppol));
  \\print(lift(toppol), " of type ", type(lift(toppol)));
  pol =  Pol(subst(Vec(lift(toppol)),t,zet));
  \\print(pol, " of type ", type(pol));
  pol1 = [p | p<- factor(pol)[,1], poldegree(p)==1][1];
  gam = -polcoef(pol1,0);
  \\ now to convert a double-decker an we list twice and substitute xet for t and gam for y:
  [subst(subst(lift(lift(an)),t,zet),y,gam) | an <- anvec];
}

nf_disc_bound = 100;
verbose=1;
number_of_an=100;

NewspaceDecompositionDimsPolysTracesCoeffs (N,G,chi, k, dmax) =
{
  if(verbose,printf("(N,k,chi)=(%d,%d,%s)",N,k,chi));
  ord = charorder(G,chi);
  if(verbose,printf(" (order(chi)=%d)\n",ord));
  ord2 = if(ord%4==2,ord/2,ord);
  cd = eulerphi(ord);
  Snew = mfinit([N, k, [G,chi]], 0);
  newforms = mfeigenbasis(Snew);
  nnf=#newforms;
  if(nnf==0,return([[],[],[],[],[]]));

  chipol=polcyclo(ord2,t);
  if(verbose,print("chipol = ",chipol));
  if(verbose,print("modulus = ",Snew.mod));
  Qchi = nfinit([chipol,nf_disc_bound]);
  pols = mfsplit(Snew,,1)[2];

  /* These are polys in y with defining the Hecke field F as a
  relative extension of Q(chi).  The coefficients either in Q or are
  polmods with modulus the cyclotomic poly chipol; BUT when F=Q(chi)
  the poly is just y so then we cannot recover the chipol from the
  poly.  */

  if(verbose,print("pols: ",pols));
  dims = [cd*poldegree(P) | P<-pols];
  if(verbose,print("dims: ",dims));
  nnf_small=#[d | d<-dims, d<=dmax];
  if(verbose,printf("Out of %d newforms, %d have dim <= %d\n", nnf, nnf_small, dmax));

/* The rels array stores "how relative" is the Hecke field K:
   0 for K = Q(chi) = Q: both extensions trivial
   1 for K > Q(chi) = Q: bottom extension trivial
   2 for K = Q(chi) > Q: top extension trivial
   3 for K > Q(chi) > Q: fully relative

   Note that we only see 0,1 when the character order is 1 or 2
   (cd==1), and only see 2,3 otherwise (cd>1)
*/

  rels = [(d>cd)+2*(cd>1) | d<-dims];
  if(verbose,print("relative extension codes: ",rels));

  \\ Compute the Fourier coeffients a_n:

  coeffs = mfcoefs(Snew,number_of_an);
  ans = vector(nnf, i, coeffs * mftobasis(Snew,newforms[i]));
  \\ Our forms are cuspidal so we delete the a_0 entry
  ans = [vecextract(L,[2..#L]) | L<-ans];

  \\ compute the absolute polys (as polys):
  polys = vector(nnf,i,relcode=rels[i]; if(relcode==3, rnfequation(Qchi,pols[i]), if(relcode==2,chipol,pols[i])));
  if(verbose&&nnf_small, printf("absolute polys (deg<=%d): %s\n",dmax,vecextract(polys,[1..nnf_small])));

  \\ compute the trace vectors:
  traces = vector(nnf,i, vector(number_of_an,j,abstrace(ans[i][j],dims[i])));
  \\ Avoid type inconsistency of a_1 leading to wrong traces:
  for(i=1,#nnf,traces[i][1]=dims[i]);
  if(verbose&&nnf_small, print("Traces:"); for(i=1,nnf_small,print(traces[i])));

  \\ apply polredbest_stable to polys of degree<=dmax
  for(i=1,nnf_small,
     polys[i]=polredbest_stable(polys[i]);
     );

  \\ convert an's to the power basis of the polredbested poly:
  for(i=1,nnf_small,
    if(rels[i]==1, ans[i] = change_basis_vec(ans[i], pols[i], polys[i]));
    if(rels[i]==2, ans[i] = change_basis_vec(ans[i], chipol, polys[i]));
    if(rels[i]==3, ans[i] = absolutize_vec(ans[i],chipol,pols[i],polys[i]));
     );
  if(verbose&&nnf_small, print("an:"); for(i=1,nnf_small,print(vecextract(ans[i],[1..5]))));

  \\ Extract power basis coefficients of all an:
  ancoeffs = [[Vec(lift(an), if(type(an)=="t_POLMOD",poldegree(an.mod),1)) | an<-ansi] | ansi <- ans];

  \\ Conmpute coefficient vectors of the absolute polys:
  polycoeffs = [Vecrev(f) | f<-vecextract(polys,[1..nnf_small])];
  if(verbose,printf("poly coeffs (deg<=%d): %s\n",dmax,vecextract(polycoeffs,[1..nnf_small])));

  \\ Atkin-Lehner eigenvalues:
  Nfact = factor(N);
  ALeigs=[]; \\ default
  if(ord==1,
  ALeigs=vector(nnf,i,[]);
  for(i=1,matsize(Nfact)[1],p=Nfact[i,1];Q=p^Nfact[i,2];
  alleigs = mfatkineigenvalues(Snew,Q);
  for(j=1,nnf,ALeigs[j]=concat(ALeigs[j],[[p,alleigs[j][1]]])));
  if(verbose,printf("AL-eigs: %s\n", ALeigs))
  );

  \\ sort (when >1 irreducible component) by lexicographical order of trace vectors:
  if(nnf>1,
   perm = vecsort(traces,,1);
   shortperm = vecextract(perm,[1..nnf_small]);
   traces = vecextract(traces,perm);
   ancoeffs = vecextract(ancoeffs,shortperm);
   dims = vecextract(dims,perm);
   polycoeffs = vecextract(polycoeffs,shortperm);
   if(ord==1,ALeigs = vecextract(ALeigs,perm));
   );

   return([traces,dims,polycoeffs,ancoeffs,ALeigs]);
}

\\ Thanks to Karim for this funtion to remove whitespace from a list:

vtostr(v) =
{ my (w, n = #v);
  if (!n, return ("")); w = vector(n);
  for (i = 1, n-1, w[i] = Str(v[i],","));
  w[n] = Str(v[n]);
  concat(w);
}

vvtostr(v,lb="[",rb="]") =
{ my (w, n = #v);
  if (!n, return (""));
  w = vector(n);
  for (i = 1, n-1, w[i] = concat([lb,vtostr(v[i]),rb,","]));
  w[n] = concat([lb,vtostr(v[n]),rb]);
  concat(w);
}

vvvtostr(v,lb="[",rb="]") =
{ my (w, n = #v);
  if (!n, return (""));
  w = vector(n);
  for (i = 1, n-1, w[i] = concat([lb,vvtostr(v[i],lb,rb),rb,","]));
  w[n] = concat([lb,vvtostr(v[n],lb,rb),rb]);
  concat(w);
}

ALstr(v) =
{ my (w, n = #v);
  if (!n, return (""));
  w = vector(n);
  for (i = 1, n-1, w[i] = concat(["[",vvtostr(v[i],"<",">"),"]",","]));
  w[n] = concat(["[",vvtostr(v[n],"<",">"),"]"]);
  concat(w);
}

fprintf(file,format,args[..]) = write(file,call(Strprintf,[format,args]));
fmt = "%d:%d:%d:%.3f:[%s]";
fmt3 = "%d:%d:%d:%.3f:[%s]:[%s]:[%s]:[%s]::[%s]";

DecomposeSpaces(filename,minN, maxN, mink, maxk, Nk2max, dmax, njobs=1, jobno=0) =
\\ Outputs N:k:i:time:dims:traces:polys with polys only for dims<=dmax
{
   screen = (filename=="");
   for(N=minN, maxN,
   if(!screen,printf("N = %d: ", N));
   G = znstar(N,1);
   Chars = DirichletCharacterGaloisReps(N);
   for(k=mink, maxk,
   if(N*k*k<=Nk2max && (N+k)%njobs==jobno,
   if(!screen,printf(" [k=%d] ", k));
   for(i=1,length(Chars),
          my (T = gettime(), dims);
          tdp = NewspaceDecompositionDimsPolysTracesCoeffs(N,G,Chars[i],k,dmax);
          traces = tdp[1];
          dims = tdp[2];
          polycoeffs = tdp[3];
          ancoeffs = tdp[4];
          ALeigs = tdp[5];
          tim = gettime()/1000;
          if(screen, printf(concat(fmt,"\n"), N,k,i, tim , vtostr(dims)),
                    fprintf(filename, fmt3,   N,k,i, tim , vtostr(dims), vvtostr(traces), ALstr(ALeigs), vvtostr(polycoeffs), vvvtostr(ancoeffs)));
   ))); if(!screen,printf("\n")));
}


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
\\ print("a=",a);
 dtop = poldegree(a.mod);
\\ print("dtop=",dtop);
 L = Vec(lift(a),dtop);
\\ print("first L = ",L);
 for(i=1,dtop,if(type(L[i])=="t_POLMOD",dbot = poldegree(L[i].mod);break));
\\ print("dbot=",dbot);
 for(i=1,dtop,if(type(L[i])=="t_POLMOD",L[i]=Vec(lift(L[i]),dbot),c=L[i];L[i]=vector(dbot,j,0);L[i][1]=c));
\\ print("last  L = ",L);
 concat(L);
}

nf_disc_bound = 100;
verbose=0;

NewspaceDecompositionDimsPolysTracesCoeffs (N,G,chi, k, dmax) =
{
  if(verbose,printf("(N,k,chi)=(%d,%d,%s)",N,k,chi));
  ord = charorder(G,chi);
  if(verbose,printf(" (order(chi)=%d)\n",ord));
  if(ord%4==2,ord=ord/2);
  cd = eulerphi(ord);
  Snew = mfinit([N, k, [G,chi]], 0);
  newforms = mfeigenbasis(Snew);
  nnf=#newforms;
  if(nnf==0,return([[],[],[],[]]));

  chipol = t;
  if(ord>2, chipol=polcyclo(ord,t));
  if(verbose,print("chipol = ",chipol));
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
  rels = [d>cd && cd>1 | d<-dims];
  if(verbose,print("genuine relative extensions: ",rels));
  nnf_small=0;
  for(i=1,nnf,if(dims[i]<=dmax,nnf_small+=1));
  if(verbose,print("Out of %d newforms, %d have dim <= %d", #newforms, nnf, dmax));

  coeffs = mfcoefs(Snew,100);
  \\ indices 0..100, we'll drop 0 later
  ans = vector(nnf, i, coeffs * mftobasis(Snew,newforms[i]));
  ans = [vecextract(L,[2..#L]) | L<-ans];
  \\ Our forms are cuspidal so we delete the a_0 entry


  \\ compute the absolute polys (as polys):
  polys = vector(nnf,i,if(rels[i], rnfequation(Qchi,pols[i]), if(ord==1,pols[i],chipol)));
  if(verbose,printf("absolute polys (deg<=%d): %s\n",dmax,vecextract(polys,[1..nnf_small])));

  coeffs=vector(nnf,i,[]);
  for(i=1,nnf, coeffs[i] = if(rels[i], [bipower_coeffs(an) | an<-ans[i]],
                             if(dims[i]==1,[[an] | an<-ans[i]],
                               [Vec(lift(an),poldegree(polys[i])) | an<-ans[i]])));

  \\ compute the trace vectors:
  traces = vector(nnf,i, vector(100,j,abstrace(ans[i][j],dims[i])));
  \\ Avoid type inconsistency of a_1 leading to wrong traces:
  for(i=1,#nnf,traces[i][1]=dims[i]);

  \\ apply polredbest_stable to polys of degree<=dmax
  for(i=1,nnf_small,polys[i]=polredbest_stable(polys[i]));
  \\ convert the absolute polys to coefficient vectors:
  polys = [Vecrev(f) | f<-polys];
  if(verbose,printf("polys (deg<=%d): %s\n",dmax,vecextract(polys,[1..nnf_small])));

  \\ sort (when >1 irreducible component) by lexicographical order of trace vectors:
  if(nnf>1,
   \\printf("\nBefore sorting:\nTraces:%s\nDims:%s\nPolys:%s",traces,dims,polys);
   perm = vecsort(traces,,1);
   traces = vecextract(traces,perm);
   coeffs = vecextract(coeffs,perm);
   dims = vecextract(dims,perm);
   polys = vecextract(polys,perm);
   \\polys = vecextract(polys,vecextract(perm,[1..nnf_small]));
   \\printf("\nAfter sorting:\nTraces:%s\nDims:%s\nPolys:%s",traces,dims,polys);
   );
   \\ omit polys of degree>dmax:
   polys=vecextract(polys,[1..nnf_small]);
   return([traces,dims,polys,coeffs]);
}

\\ Thanks to Karim for this funtion to remove whitespace from a list:

vtostr(v) =
{ my (w, n = #v);
  if (!n, return ("")); w = vector(n);
  for (i = 1, n-1, w[i] = Str(v[i],","));
  w[n] = Str(v[n]);
  concat(w);
}

vvtostr(v) =
{ my (w, n = #v);
  if (!n, return (""));
  w = vector(n);
  for (i = 1, n-1, w[i] = concat(["[",vtostr(v[i]),"],"]));
  w[n] = concat(["[",vtostr(v[n]),"]"]);
  concat(w);
}

vvvtostr(v) =
{ my (w, n = #v);
  if (!n, return (""));
  w = vector(n);
  for (i = 1, n-1, w[i] = concat(["[",vvtostr(v[i]),"],"]));
  w[n] = concat(["[",vvtostr(v[n]),"]"]);
  concat(w);
}

fprintf(file,format,args[..]) = write(file,call(Strprintf,[format,args]));
fmt = "%d:%d:%d:%.3f:[%s]";
fmt3 = "%d:%d:%d:%.3f:[%s]:[%s]:[%s]::[%s]";

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
          polys = tdp[3];
          coeffs = tdp[4];
          tim = gettime()/1000;
          if(screen, printf(concat(fmt,"\n"), N,k,i, tim , vtostr(dims)),
                    fprintf(filename, fmt3,  N,k,i, tim , vtostr(dims), vvtostr(traces), vvtostr(polys), vvvtostr(coeffs)));
   ))); if(!screen,printf("\n")));
}

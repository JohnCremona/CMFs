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

NewspaceDecompositionDimsPolysTraces (N,G,chi, k, dmax) =
{
  cd = eulerphi(charorder(G,chi));
  Snew = mfinit([N, k, [G,chi]], 0);
  newforms = mfeigenbasis(Snew);
  coeffs = mfcoefs(Snew,100); \\ indices 0..100, we'll drop 0 later
  pols = mfsplit(Snew,,1)[2];
  dims = [cd*poldegree(P) | P<-pols];
  nnf=#newforms;
  nnf_small=0;
  for(i=1,nnf,if(dims[i]<=dmax,nnf_small+=1));
  \\print("Out of %d newforms, %d have dim <= %d", #newforms, nnf, dmax);
  ans = vector(nnf, i, coeffs * mftobasis(Snew,newforms[i]));
  traces = vector(nnf,i, Vec(apply((a->abstrace(a,dims[i])),ans[i])));
  \\ Our forms are cuspidal so we delete the a_0 entry:
  traces = [vecextract(L,[2..#L]) | L<-traces];
  \\ Avoid type inconsistency of a_1 leading to wrong traces:
  for(i=1,#traces,traces[i][1]=dims[i]);
  polys = vector(nnf_small,i,Vecrev(Absolutise(G,chi,pols[i])));
  if(nnf>1,
   \\printf("\nBefore sorting:\nTraces:%s\nDims:%s\nPolys:%s",traces,dims,polys);
   perm = vecsort(traces,,1);
   traces = vecextract(traces,perm);
   dims = vecextract(dims,perm);
   polys = vecextract(polys,vecextract(perm,[1..nnf_small]));
   \\printf("\nAfter sorting:\nTraces:%s\nDims:%s\nPolys:%s",traces,dims,polys);
   );
  return([traces,dims,polys]);
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

fprintf(file,format,args[..]) = write(file,call(Strprintf,[format,args]));
fmt = "%d:%d:%d:%.3f:[%s]";
fmt3 = "%d:%d:%d:%.3f:[%s]:[%s]:[%s]:";

DecomposeSpaces(filename,minN, maxN, mink, maxk, Nkmax, dmax) =
\\ Outputs N:k:i:time:dims:traces:polys with polys only for dims<=dmax
{
   screen = (filename=="");
   for(N=minN, maxN,
   if(!screen,printf("N = %d: ", N));
   G = znstar(N,1);
   Chars = DirichletCharacterGaloisReps(N);
   for(k=mink, maxk,
   if(N*k<=Nkmax,
   if(!screen,printf(" [k=%d] ", k));
   for(i=1,length(Chars),
          my (T = gettime(), dims);
          tdp = NewspaceDecompositionDimsPolysTraces(N,G,Chars[i],k,dmax);
          dims = tdp[2];
          traces = tdp[1];
          polys = tdp[3];
          t = gettime()/1000;
          if(screen, printf(concat(fmt,"\n"), N,k,i, t , vtostr(dims)),
                    fprintf(filename, fmt3,  N,k,i, t , vtostr(dims), vvtostr(traces), vvtostr(polys)));
   ))); if(!screen,printf("\n")));
}

fmt2 = "%d:%d:%d:[%s]:[%s]";
DecomposeCharSpaces(filename,N,k,ch,dmax) =
{
   screen = (filename=="");
   if(!screen,printf("N = %d: ", N));
   G = znstar(N,1);
   Chars = DirichletCharacterGaloisReps(N);
   chi=Chars[ch];
   if(!screen,printf(" [k=%d] ", k));
   my (T = gettime(), dims_polys);
   dims_polys = NewspaceDecompositionWithPolys(N,G,chi,k,dmax);
   dims  = dims_polys[1];
   polys = dims_polys[2];
   t = gettime()/1000;
   if(screen, printf(concat(fmt2,"\n"), N,k,ch, dims, polys), fprintf(filename, fmt2,  N,k,ch, vtostr(dims), vtostr(polys)));
   if(!screen,printf("\n"));
}

Traces(filename,N,k,ch,dmax) =
{
   screen = (filename=="");
   if(!screen,printf("N = %d: ", N));
   G = znstar(N,1);
   Chars = DirichletCharacterGaloisReps(N);
   chi=Chars[ch];
   if(!screen,printf(" (N,k,chi)=(%d,%d,%d) ", N,k,ch));
   my (T = gettime(), dims_polys);
   dims_traces = NewspaceDecompositionWithTraces(N,G,chi,k,dmax);
   dims  = dims_traces[1];
   traces = dims_traces[2];
   t = gettime()/1000;
   if(screen, printf(concat(fmt2,"\n"), N,k,ch, dims, traces), fprintf(filename, fmt2,  N,k,ch, vtostr(dims), vtostr(traces)));
   if(!screen,printf("\n"));
}

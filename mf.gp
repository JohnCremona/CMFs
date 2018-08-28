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

DirichletCharacterGaloisReps(N) =
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

Absolutise(G, chi, f, flag=0) =
{
 ord = charorder(G,chi);
 field = polytype(f);
 if(field=="Q", if(ord<=2, pol=f, Qchi=nfinit(polcyclo(ord,xx));pol=rnfequation(Qchi,f)),
                Qchi=nfinit(field);pol=rnfequation(Qchi,f));
 if(flag,pol=polredabs(pol),pol=polredbest(pol));
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

NewspaceDecompositionWithTraces (N,G,chi, k, dmax) =
{
  cd = eulerphi(charorder(G,chi));
  Snew = mfinit([N, k, [G,chi]], 0);
  newforms = mfeigenbasis(Snew);
  coeffs = mfcoefs(Snew,100);
  pols = mfsplit(Snew,,1)[2];
  dims = [cd*poldegree(P) | P<-pols];
  nnf=0;
  for(i=1,#newforms,if(dims[i]<=dmax,nnf+=1));
  \\print("Out of %d newforms, %d have dim <= %d", #newforms, nnf, dmax);
  an_lists = vector(nnf, i, coeffs * mftobasis(Snew,newforms[i]));
  \\print("an:");
  \\for(i=1,nnf,print(an_lists[i]));
  traces = [apply(trace,ans) | ans<-an_lists];
  \\print("Tr(an):");
  \\for(i=1,nnf,print(traces[i]));
  return ([dims,traces]);
}

\\ Thanks to Karim for this funtion to remove whitespace from a list:

vtostr(v) =
  { my (w, n = #v);
    if (!n, return (""));
    w = vector(n);
    for (i = 1, n-1, w[i] = Str(v[i],","));
    w[n] = Str(v[n]);
    concat(w);
  }

fprintf(file,format,args[..]) = write(file,call(Strprintf,[format,args]));
fmt = "%d:%d:%d:%.3f:[%s]";

DecomposeSpaces(filename,minN, maxN, mink, maxk) =
{
   screen = (filename=="");
   for(N=minN, maxN,
   if(!screen,printf("N = %d: ", N));
   G = znstar(N,1);
   Chars = DirichletCharacterGaloisReps(N);
   for(k=mink, maxk,
   if(!screen,printf(" [k=%d] ", k));
   for(i=1,length(Chars),
          my (T = gettime(), X);
          X = NewspaceDecomposition(N,G,Chars[i],k);
          t = gettime()/1000;
          if(screen, printf(concat(fmt,"\n"), N,k,i, t , X), fprintf(filename, fmt,  N,k,i, t , vtostr(X)));
   )); if(!screen,printf("\n")));
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

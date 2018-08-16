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
  print(pols);
  return ([cd*poldegree(P) | P<-pols]);
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
   scr = (filename=="");
   for(N=minN, maxN,
   if(!scr,printf("N = %d: ", N));
   G = znstar(N,1);
   Chars = DirichletCharacterGaloisReps(N);
   for(k=mink, maxk,
   if(!scr,printf(" [k=%d] ", k));
   for(i=1,length(Chars),
          my (T = gettime(), X);
          X = NewspaceDecomposition(N,G,Chars[i],k);
          t = gettime()/1000;
          if(scr, printf(concat(fmt,"\n"), N,k,i, t , X), fprintf(filename, fmt,  N,k,i, t , vtostr(X)));
   )); if(!scr,printf("\n")));
}

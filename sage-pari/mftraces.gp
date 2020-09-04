
CharacterTraces(N, G, chi) =
{
    my(d,z,v);
    d = G[2][1];
    z = Mod(x, polcyclo(d));
    v = vector(N,j,trace(chareval(G,chi,j-1,[z,d])));
    return(v);
}

CharacterOrbitReps(N) =
{
    my(ZNstar,Chars,nChars,vv,sChars);
    ZNstar = znstar(N,1);
    Chars = chargalois(ZNstar);
    nChars = length(Chars);
    vv = vecsort(vector(nChars, i,  [concat([charorder(ZNstar,Chars[i])],CharacterTraces(N,ZNstar,Chars[i])), i] ));
    sChars = vector(nChars, i, Chars[vv[i][2]]);
    return(sChars);
}

ZNstar(N) = { return(znstar(N,1)); }

Newspace(N,k,o) = { return(mfinit([N,k,[ZNstar(N),CharacterOrbitReps(N)[o]]],0)); }

Newforms(S) = { return(mfeigenbasis(S)); }

QDimension(S,N,o) = { return(mfdim(S)*eulerphi(charorder(znstar(N,1),CharacterOrbitResp(N)[o]))); }

abstrace(x, cd) =
{
  my(y);
  if(type(x)=="t_INT",return(cd*x));
  y=trace(x);
  if(type(y)=="t_POLMOD",y=trace(y));
  return(y);
}

ConreyCharacter(q,n) = { return(znconreychar(znstar(q,1),m)); }

Traces(N,k,chi,n) =
{
    my(G,cd,an,v);
    G = znstar(N,1);
    cd = eulerphi(charorder(G,chi));
    v = mfcoefs(mftraceform([N,k,[G,chi]]),n);
    return(vector(n,j,abstrace(v[j+1],cd)));
}

vtostr(v) =
{
    my (w, n = #v);
    if (!n, return ("")); w = vector(n);
    for (i = 1, n-1, w[i] = Str(v[i],","));
    w[n] = Str(v[n]);
    return(concat(["[",concat(w),"]"]));
}

fprintf(file,format,args[..]) = write(file,call(Strprintf,[format,args]));

DumpTraces(outfile,N,k,o,n) =
{
    my(chis,t=gettime(),T);
    chis = CharacterOrbitReps(N);
    chi = chis[o];
    T = Traces(N,k,chis[o],n);
    if (T[1] > 0,
        t = gettime()/1000;
        fprintf(outfile,"%d:%d:%d:%.3f:%s",N,k,o,t,length(T));
    );
    return(1.0*t);
}

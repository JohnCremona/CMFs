\\ gp script from Karim:

\\Here's a simpler program that outputs the dimensions of
\\Hecke-irreducible subspaces:

dims(N = 2^2 * 3 * 7, k=4) =
{ my(G, L);
  G = znstar(N, 1);
    L = [[G,chi] | chi <-chargalois(G)]; \\, !zncharisodd(G,chi)];
      for (i = 1, #L,
          my (T = gettime(), Snew, d, pols);
              Snew = mfinit([N, k, L[i]], 0);
                  d = mfdim(Snew); if (!d, next);
                      pols = mfsplit(Snew,,1)[2];
                          printf("%4ld %6ld : %.3fs,  dims = %s\n", i,
                          d, gettime()/1000. , [poldegree(P) | P<-pols]);
                                                                     );
}

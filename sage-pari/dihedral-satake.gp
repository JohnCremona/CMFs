/* We always want to allow ramification at real places */
bnrnarrowinit(F,id)=bnrinit(F,[id,vector(F.r1,i,1)],1);

/* Given a rayclass char chi, return the induced character mod a principal ideal of smallest possible norm */
charinduce(R,chi)=
{
	my(B,q,ids,m,R2,v);
	B=16; q=1;
	while(1,
		ids=ideallist(R.bnf,B,0);
		while(q<=#ids,
			for(i=1,#ids[q],
				/* find a principal ideal divisible by our given ideal */
				m=idealmul(R.bnf,R.mod[1],ids[q][i].mod[1]);
				if(bnfisprincipal(R.bnf,m,0)==0,
					R2=bnrnarrowinit(R.bnf,m);
					v=apply(x->chareval(R,chi,x),R2.clgp[3]);
					return([R2,bnrchar(R2,R2.clgp[3],v)[1]]);
				);
			);
			q++;
		);
		B*=2;
	);
}

/* conjugate of ideal x in a quadratic field F */
idealconj(F,x)=idealdiv(F,idealnorm(F,x),x,1);

/* chi(x)/chi(conjugate(x)) */
charprojeval(R,chi,x)=
{
	my(t);
	t=chareval(R,chi,x)-chareval(R,chi,idealconj(R.bnf,x));
	t-floor(t)
}

/* Given a rayclass character chi, return the rayclass character whose Artin rep has image equal to the projective image of chi */
charproj(R,chi)=
{
	my(m,v,R2,chi2,R3,chi3);
	m=idealmul(R.bnf,R.mod[1],idealconj(R.bnf,R.mod[1]));
	R2=bnrnarrowinit(R.bnf,m);
	v=apply(x->charprojeval(R,chi,x),R2.clgp[3]);
	chi2=bnrchar(R2,R2.clgp[3],v)[1];

	\\ repeat calculation with smallest possible modulus
	m=bnrconductorofchar(R2,chi2);
	if(!issquare(idealnorm(R.bnf,m),&m),
		error("nonsquare norm in charproj");
	);
	R3=bnrnarrowinit(R.bnf,m);
	chi3=bnrchar(R3,R2.clgp[3],v)[1];
	[R3,chi3,m]
}

/* Returns the nebntypus (character) of the correspondind modular form along with its Conrey label */
nebentypus(L)=
{
	my(N,sden,snum,R,g,v);
	N=L[1][1]; sden=L[2]; snum=L[3];

	/* Create narrow ray class group of modulus N for Q, aka (Z/NZ)* */
	R=bnrnarrowinit(bnfinit(x),N);

	/* compute list of prime generators for (Z/NZ)* so we can extract character values from Satake parameters */
	g=[]; forprime(p=2,N,if(#bnrchar(R,g)==1,break);if(N%p,g=concat(g,[p])););

	/* compute determinant e(a)e(b)=e(a+b) in terms of Satake params [a,b] at primes p in g */
	v=apply(x->vecsum(snum[primepi(x)])/sden,g);

	/* return Conrey label of the corresponding Dirichlet character */
	Strprintf("%d.%d",N,znconreyexp(znstar(N,1),bnrchar(R,g,v)[1]))
}

append(L,v)=
{
	my(i,s,m,n);
	if(!v[1][3],return(L)); 				/* skip non-cuspidal forms */
	m=length(v[3]); n=v[2];
	for(i=1,length(L),						/* for each L-function of this conductor */
		if(L[i][2]==n,						/* if Satake denominators match */
			for(e=1,n-1,if(gcd(e,n)==1,		/* for e coprime to n */
				for(j=1,m,					/* for each Satake parameter */
					if(vecsort(apply(x->(e*x)%n,v[3][j]))!=L[i][3][j],break());
					/* if all the ap's match we assume the L-function is conjugate (true if m exceeds the Sturm bound, but this is not verified) */
					if(j==m,
						if(Set(L[i][1][4])!=Set(concat(L[i][1][4],v[1][4])),L[i][1][4]=concat(L[i][1][4],v[1][4]));
						L[i][1][15]+=v[1][15];	/* add times for conjugate reps */
						if(e==1,L[i][1][16]++);	/* increment count of times we have seen this exact L-function */
						L[i][1][17]++;			/* increment count of times we have seen a conjugate of this L-function */
						return(L);
					);
				);
			));
		);
	);
	s=v[1];
	print(strjoin(strsplit(Str(s[1]":"s[2]":"s[3]":"s[4]":"s[5]":"s[6]":"s[7]":"s[8]":"s[9]":"s[10]":"s[11]":"s[12]":"s[13]":"s[14]":"s[15]":"s[16]":"s[17]":"v[2])," "),""));
	concat(L,[v])
}

/* return L-function data; chi is assumed to be primitive */
Lfunction(R,chi,nprimes,proj=0)=
{
	my(i,p,L,c,a,s,t,irred,R2,chi2,ker2,m2,deg2,n);
	L=vector(nprimes); 			 /* vector of satake-parameters, one for each prime */
	c=bnrconductorofchar(R,chi); /* conductor of ray class character */
	t=getabstime();
	irred=0; irred2=0;
	for(i=1,nprimes,
		p=prime(i);
		P=idealprimedec(R.bnf,p); 				 /* decompose prime over quadratic field */
		L[i]=[]; 								 /* will be list of 0,1,2 Satake parameters, at good primes 2, at bad primes 0 or 1 */
		for(j=1,length(P), 						 /* for each prime above p */
			if(idealval(R.bnf,c[1],P[j])==0, 	 /* is P[j] prime to the conductor (of the ray class character)? */
				a=chareval(R,chi,P[j]);
				L[i]=concat(L[i],if(P[j].f==2,[a/2,(a+1)/2],a)); /* split primes will get hit twice, inert just once */
			);
		);
		/* the associated modular form is cuspidal (artin rep is irreducible) if and only if chi differs from its Galois conjugate */
		if(length(P)==2 && (length(L[i])==1 || (length(L[i])==2 && L[i][1]!=L[i][2])), irred=1);
		\\ if(length(P)==2 && ((length(L[i])==2 && L[i][1]!=L[i][2] && abs(L[i][2]-L[i][1])!=1/2)), irred2=1);
		L[i]=vecsort(L[i]);
	);
	n=denominator(L);
	L=apply(a->apply(x->((n*x)%n),a),L);

	/* To avoid squaring the modulus, trust caller if proj is set */
	if(proj,
		m2=bnrconductorofchar(R,chi);
		if(!issquare(idealnorm(R.bnf,m2),&m2),error("nonsquare norm in Lfunction"));
		[R2,chi2]=[R,chi];
	,
		[R2,chi2,m2]=charproj(R,chi);
	);
	s=[
		idealnorm(R.bnf,c[1])*abs(R.bnf.disc),   /* conductor of Artin rep / level of weight 1 modular form */
		if(R.bnf.r1==0,[0,1],vecsort(c[2])),     /* gamma factor shifts */
    	irred, 									 /* cuspidal/irreducible */
    	[R.bnf.disc], 							 /* discriminant of quadratic field */
    	R.clgp[2], 								 /* elementary divisors of ray class group */
    	chi, 									 /* ray class character (values on generators) */
    	charorder(R.clgp[2],chi),				 /* order of ray class character */
    	ker=charker(R.clgp[2],chi),				 /* kernel of ray class character (relative to generators corresponding to elementary divisors) */
    	bnrclassno(R,ker),						 /* relative degree of field cut out by ray class character */
    	m2,										 /* modulus of projective rep */
    	R2.clgp[2],								 /* elementary divisors of projective ray class group */
    	chi2,									 /* projective ray class character */
    	ker2=charker(R2.clgp[2],chi2),			 /* kernel of projective ray class character */
    	bnrclassno(R2,ker2),					 /* relative degree of field cut out by projective ray class character */
    	getabstime()-t,	 						 /* cpu time to compute this L-function */
    	1,										 /* count identical L-functions */
    	1										 /* count conjugate L-functions */
	];
	[s,n,L]
}

/* B is a bound on the conductor of the artin-rep, nprimes is the number of primes at which to compute Satake parameters */
rayclasses(B,nprimes,justone=0,jobs=1,jobid=0)=
{
	my(d,F,ids,m,R,c,k,L,N);
	if(justone,jobs=1;jobid=0);
	L=vector(B,q,[]);
	for(absd=1,B,forstep(sgnd=-1,1,2, 			/* iterate over quadratic discriminants d=sgnd*absd for |d|=absd <= B */
		d=sgnd*absd; 							/* discriminant of quadratic field */
		if(isfundamental(d) && d != 1,  		/* we only want fundamental non-trivial discs */
			F=bnfinit(X^2-d,1); 				/* quadratic field F of discriminant d */
			ids=ideallist(F,floor(B/absd),0); 	/* iterate over OK-ideals of norm <= B/|d| */
			for(q=1,length(ids), 				/* q is the norm of ideal (conductor of primitive ray class character) */
				N=absd*q;						/* conductor of artin rep is |d|*N(id) */
				/* split work across jobs by artin rep conductor (important) */
				if((!justone||N==B)&&(N%jobs==jobid),
					for(j=1,length(ids[q]), 	/* j indexes ideals of norm q */
						m=ids[q][j].mod[1];		/* m is the modulus (generalized ideal) for the ray class character */
						R=bnrnarrowinit(F,m); 	/* create ray class group structure */
						c=bnrchar(R,[]); 		/* create group of ray class characters (characters of the ray class group) */
						for(k=1,length(c), 		/* for each ray class character */
							if(idealnorm(F,bnrconductorofchar(R,c[k]))==q, 			/* restrict to primitive characters */
								L[N]=append(L[absd*q],Lfunction(R,c[k],nprimes,0)); /* L-function of Artin rep for this ray class character */
							);
						);
					);
				);
			);
		);
	));
	concat(L)
}

/* Given conductor bound B, number of Satake-parameters (-1) and file name, output a list of all odd irred 2-dim dihedral Artin reps of conductor up to B. */
go(B,n,filename,justone=0,jobs=1,jobid=0)=
{
	my(v,nprimes,gshift,N,D,G,rchi,ordrchi,key,deg,pmod,PG,pchar,pker,pkerp,pdeg,chi,t,cnt,dim,sden,snum,rec);
	if(jobs>1,filename=Str(filename"_"jobid));
	nprimes=primepi(n);
	system("rm -f "filename);
	v=rayclasses(B,nprimes,justone,jobs,jobid);
	for(i=1,#v,
	    gshift=v[i][1][2];							/* (1) Gamma factor shifts, [0,1] in the odd case, [0,0] or [1,1] in the even case  */
		N=v[i][1][1]; 								/* (2) conductor of Artin rep (disc(K)*conductor of ray class character)*/
		D=v[i][1][4]; 								/* (3) discs of quadratic fields K over which dihedral Artin field is abelian (1 or 3 discs) */
		G=v[i][1][5]; 								/* (4) elementary divisors of ray class group */
		rchi=v[i][1][6]; 							/* (5) ray class character */
		ordrchi=v[i][1][7];							/* (6) order of ray class character */
		ker=v[i][1][8];								/* (7) kernel of ray class character */
		deg=v[i][1][9];								/* (8) relative degree of kernel field (abelian over K but need not be Galois over Q!) */
		pmod=v[i][1][10]; 							/* (9) modulus of projective character */
		PG=v[i][1][11];								/* (10) elementary divisors of projective ray class group */
		pchar=v[i][1][12];							/* (11) projective ray class character */
		pker=v[i][1][13];							/* (12) kernel of projective ray class character */
		pdeg=v[i][1][14];							/* (13) relative degree of projective kernel field (as a cyclic ext of quad field K) */
		chi=nebentypus(v[i]);					    /* (14) Determinant character of artin rep */
		t=v[i][1][15];								/* (15) cputime to compute this artin rep (and all its duplicates/conjugates), in milliseconds */
		cnt=v[i][1][16];							/* (16) total number of L-functions computed that are conjugate to this one */
		dim=v[i][1][17]/cnt;						/* (17) number of distinct conjugates of this L-function */
		sden=v[i][2];								/* (18) common denominator n of Satake parameters (traces are sums of nth roots of unity) */
		snum=v[i][3][2..#v[i][3]];	 				/* (19) numerators of Satake params at finite primes (a_p = zeta_n^a + zeta_n^b for param [a,b]) */
		rec=Str(gshift":"N":"D":"G":"rchi":"ordrchi":"ker":"deg":"pmod":"PG":"pchar":"pker":"pdeg":"chi":"t":"cnt":"dim":"sden":"snum);
		write(filename,strjoin(strsplit(rec," "),""));
	);
	if(!justone,print("Done!"));
}

/*
   Given a quadratic discriminant D, modulus m, and congruence subgroup H of modulus m,
   returns the relative degree of the correponding quotient of the ray class group of modulus m.
*/
projclassno(D,m,H)=
{
	my(F,R,f);
	if(#D==3,print(2);return(2));
	F=bnfinit(X^2-D[1],1);
	R=bnrnarrowinit(F,m);
	f=bnrclassno(R,H);
	print(f);
	f;
}

/* Given f in (Q[X])[x] an g in Q[x] returns a poly in Q[x] which is either f (if f is constant as a poly in X) or res(f,g,X) */
descend(f,g)=if(polcoeff(f,1,X)==0,f,polresultant(g,f,X));	

polredbestabs(f)={f=polredbest(f);if(poldegree(f)<=64,polredabs(f),polredbestf(f))}

/*
   Given a list of quadratic discriminants D associated to a dihedral ray class field (so 1 or 3 in the D2 case), a  modulus m,
   and a congruence subgroup H of modulus m, returns a list of Galois polynomials over QQ whose compositum is the dihedral field.
*/
projclassfield(D,m,H)=
{
	my(F,R,fs,g,t);
	t=getabstime();
	if(#D==3,
		f=[x^2-D[1],x^2-D[2]];
		t=getabstime()-t;
		print(f":"t);
		return(f);
	);
	if(#D!=1,error("projclassfield expects a vector with one or three integer discriminants, got: "D));
	g=X^2-D[1];
	F=bnfinit(g,1);
	R=bnrnarrowinit(F,m);
	fs=concat([x^2-D[1]],apply(f->polredbestabs(descend(f,g)),bnrclassfield(R,H)));
	t=getabstime()-t;
	print(fs":"t);
	fs;
}

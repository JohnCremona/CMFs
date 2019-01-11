characters(d) =
{
	local(m,c,answer,j,k,a);

	m=length(d);
	if(m==0,
		answer=[[]];
	,
		c = characters(vector(m-1,j,d[j]));
		answer = vector(length(c)*d[m]);
		for(a=0,d[m]-1,
			for(j=1,length(c),
				answer[a*length(c)+j]= vector(m,k,if(k<m,c[j][k],a));
			);
		);
	);
	answer
}

dot(x,y,w) =
{
	local(s,j);
	s=sum(j=1,length(x),x[j]*y[j]/w[j]);
	s-truncate(s)
}

append(L,v)=
{
	local(i);
	if(!v[1][3],return(L)); /* prune non-cuspidal forms */
	for(i=1,length(L),if(L[i]==v,return(L)));
	vector(length(L)+1,i,if(i>length(L),v,L[i]))
}

/* return L-function data; chi is assumed to be primitive */
Lfunction(R,chi,nprimes)=
{
	local(i,p,L,c,a,selberg);
	L=vector(nprimes);
	c=bnrconductorofchar(R,chi);
	selberg=[
		idealnorm(R.bnf,c[1])*abs(R.bnf.disc),   /* level */
		L[1]=if(R.bnf.r1==0,[0,1],vecsort(c[2])), /* gamma factor shifts */
    0  /* whether or not cuspidal (determined below) */
	];
	for(i=1,nprimes,
		p=prime(i);
		P=idealprimedec(R.bnf,p);
		L[i]=[];
		for(j=1,length(P),
			if(idealval(R.bnf,c[1],P[j])==0,
				a=dot(chi,bnrisprincipal(R,P[j],0),R.clgp[2]);
				L[i]=concat(L[i],if(P[j].f==2,[a/2,(a+1)/2],a));
			);
		);
		/* the associated modular form is cuspidal if and
		   only if chi differs from its Galois conjugate */
		if(length(P)==2 && 
		(length(L[i])==1 || (length(L[i])==2 && L[i][1]!=L[i][2])),selberg[3]=1);
		L[i]=vecsort(L[i]);
	);
	[selberg,L]
}

rayclasses(B,nprimes)=
{
	local(absd,sgnd,d,F,ids,q,m,R,c,i,j,k,L,v);
	L=vector(B,q,[]);
	for(absd=1,B,
	forstep(sgnd=-1,1,2,
		d=sgnd*absd;
		if(isfundamental(d) && d != 1,
			F = bnfinit(X^2-d);
			ids = ideallist(F,floor(B/absd),0);
			/* ideallistarch appears to be broken */
			/*ids=ideallistarch(F,ids,vector(F.r1,j,1));*/
			for(q=1,length(ids),
			for(j=1,length(ids[q]),
				m=ids[q][j].mod;
				if(d>0,m[2]=[1,1]);
				R=bnrinit(F,m,1);
				c=characters(R.clgp[2]);
				for(k=1,length(c),
					if(idealnorm(F,bnrconductorofchar(R,c[k]))==q,
						L[absd*q]=append(L[absd*q],Lfunction(R,c[k],nprimes));
					);
				);
			);
			);
		);
	);
	);
	k=sum(i=1,length(L),length(L[i]));
	v=vector(k);
	i=0;
	for(q=1,length(L),
	for(j=1,length(L[q]),
		i++;
		v[i]=[L[q][j][1][1],concat([L[q][j][1][2]/2],L[q][j][2])];
	);
	);
	v
}

nebentypus(L)=
{
	local(N,v,z,f,t,answer);
	N=L[1];
	v=L[2][2..#L[2]];
	z=apply(x->lift(x),znstar(N)[3]);
	answer=[];
	for(i=1,#z,
		f=factor(z[i]);
		t=sum(j=1,#f[,1],vecsum(v[primepi(f[j,1])])*f[j,2]);
		t-=truncate(t);
		answer=concat(answer,[[z[i],t]]);
	);
	answer
}

go(B,nprimes,filename)=
{
	local(v,N,chi,satake);
	system("rm -f "filename);
	v=select(x->vecsum(x[2][1])*2%2,rayclasses(B,nprimes));
	for(i=1,#v,
		N=v[i][1];
		chi=nebentypus(v[i]);
		satake=v[i][2][2..#v[i][2]];
		write(filename,[N,chi,satake]);
	);
}

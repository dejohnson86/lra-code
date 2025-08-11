import time

def l2(n):
	m=log(abs(n),2)
	return(RR(m))

def SIS(vv):
	for i in range(2,len(vv)):
		if sum(vv[:i])>=vv[i]:
			return(False)
	return(True)

def MC(vv,mr):
	for i in range(len(vv)):
		vv[i]=Mod(vv[i],mr).lift_centered()
	return(vv)	

def SV(vv):
	va=[]
	for i in range(len(vv)):
		va+=[(vv[i],i)]
	return(sorted(va))	

########
## Unshuffled Merkle-Hellman Public Key Generator
##

def pkMH(n):
	N=2^n
	a=[]
	for i in range(1,n+1):
		a+=[randint((2^(i-1)-1)*N,(2^(i-1))*N)]
	M=randint(2*N^2+1,4*N^2-1)
	W=0
	while (gcd(W,M)!=1):
		W=randint(2,M-2)
	a=vector(a)
	pk=W*a%M
	##return(pk)
	
	return(pk,a,W,M)	
	
########
## Shuffled Merkle-Hellman Public Key Generator
##

def pkMHS(n):
	N=2^n
	a=[]
	for i in range(1,n+1):
		a+=[randint((2^(i-1)-1)*N,(2^(i-1))*N)]
	M=randint(2*N^2+1,4*N^2-1)
	W=0
	while (gcd(W,M)!=1):
		W=randint(2,M-2)
	a=vector(a)
	b=copy(a)
	shuffle(b)
	pk=W*b%M
	pko=W*a%M
	u=xgcd(W,M)[1]
	return(pk,b,a,u,M,W,list(pko))
	
	

########
## Discriminator Matrix Functions for Merkle-Hellman
##

def DmatrixMH(pkL):
	rl=[]
	r2=[]
	lr=len(pkL)
	LY=xgcdListMerk(pkL)
	ln=len(LY)
	for i in range(ln):
		for j in range(i+1,ln):
			if LY[i][2][0]==LY[j][2][0]:
				rl+=[eqsmMerk(LY[i],LY[j],lr)]
	r1=matrix(ZZ,rl)
	r1=r1.echelon_form()
	r1=r1[:r1.rank()]
	return(r1)

def xgcdListMerk(LP):
	coll=[]
	lr=len(LP)
	for i in range(lr-1):
		for j in range(i+1,lr):
			coll+=[[i,j,xgcd(LP[i],LP[j])]]
	return(coll)

def eqsmMerk(L1,L2,lr):
	fineq=[0 for i in range(lr)]
	g0123=[L1[2][1],L1[2][2],L2[2][1],L2[2][2]]
	for i in range(4):
		if i<2:
			fineq[L1[i]]+=g0123[i]
		else:
			fineq[L2[i%2]]-=g0123[i]
	return(fineq)

########
## LRA-MHU Single Execution using d coefficients of the public key
##

def LRAMHU(pk,d):
	timestart=time.time()
	pkn=pk[:d]
	D=DmatrixMH(pkn)
	L=D.LLL()
	K=L[:L.nrows()-1].right_kernel().matrix()
	E=K.echelon_form()
	rtv=E.solve_left(pkn)
	r2=rtv[0]
	t2=rtv[1]
	ind=0
	g=xgcd(r2,t2)
	h2=g[1]
	va=h2*pk%t2
	
	timefinish=time.time()-timestart
	
	successSum=(sum(va)<t2)
	successSIS=SIS(va)
	success=(successSIS and successSum)
	return(success,timefinish)	
			
	
########
## LRA-MHU Mass Tester on public keys with n coefficients and discriminator matrix degree d
##

def MerkULRAMass(ntests,n,d):
	
	totsuccess=0
	tottime=0
	for i in range(ntests):
		pk=pkMHU(n)
		X=LRAMHU(pk[0],d)
		if X[0]:
			totsuccess+=1
		tottime+=X[1]
	print("LRA of degree",d,"succeeded against Merkle-Hellman degree",n)
	print("with success ratio",RR(totsuccess/ntests))
	print("and average time",RR(tottime/ntests))	
	
########
## Efficient Polynomial Time Attack Simulator
##

def EPTAS(pk,n):
	timestart=time.time()
	
	pkn=pk[1:n]
	D=diagonal_matrix([-pk[0] for i in range(n-1)])
	D=D.stack(vector(pkn))
	L=matrix(ZZ,D,sparse=False).LLL()
	
	timefinish=time.time()-timestart
	
	return(timefinish)

def EPTAMass(ntests,n,d):
	tottime=0
	for i in range(ntests):
		pk=pkMH(n)	
		tottime+=EPTAS(pk,d)
	
	print("EPTA of degree",d,"against Merkle-Hellman degree",n)
	print("has average time",RR(tottime/ntests))	


def mhdecr(sv,ri,t,c):
	cr=ri*c%t
	mi=zero_vector(len(sv))
	for i in range(len(sv)-1,-1,-1):
		if (cr>sv[i]):
			mi[i]=1
			cr=cr-sv[i]
	return(mi)		
	
	
########
## LRA-MHS Mass Tester on public keys with n coefficients and discriminator matrix degree d
##

def LRAF(pkn):
	D=DmatrixMH(pkn)
	L=D.LLL()
	K=L[:L.nrows()-1].right_kernel().matrix()
	E=matrix(ZZ,K).echelon_form()
	rtv=E.solve_left(pkn)
	r2=rtv[0]
	t2=abs(rtv[1])
	g=xgcd(r2,t2)
	h2=g[1]
	return(h2,t2)

def MReorg(E,pkv):
	E=E.echelon_form()
	E1=SV(E[0])
	pks=vector([pkv[E1[i][1]] for i in range(len(pkv))])
	e1=vector([E[0][E1[i][1]] for i in range(len(pkv))])
	e2=vector([E[1][E1[i][1]] for i in range(len(pkv))])
	E=matrix(ZZ,[e1,e2])
	return(E.echelon_form(),pks)

def MPi(M,pkV,pe):
	e1=vector([M[0][i] for i in pe])
	e2=vector([M[1][i] for i in pe])
	pke=vector([pkV[i] for i in pe])
	N=matrix(ZZ,[e1,e2])	
	N=N.echelon_form()
	cfv=N.solve_left(pke)
	print(N)
	r2=cfv[0]
	t2=abs(cfv[1])
	g=xgcd(r2,t2)
	h2=-abs(g[1])		
	return(h2,t2)


def MPp(pkV,pe):
	pke=vector([pkV[i] for i in pe])
	return(pke)


def FTest(Ma):
	N=Ma.transpose()
	CN=N.rows()
	shuffle(CN)
	E=matrix(ZZ,CN).transpose()
	HH=E[:2].echelon_form()
	HH=HH.stack(E[2])
	cfv=HH.solve_left(HH[2])
	r2=cfv[0]
	t2=abs(cfv[1])
	g=xgcd(r2,t2)
	h2=-abs(g[1])		
	return(h2,t2,HH)

def LRAInter(pk,d):
	pkn=[]
	while len(pkn)<d:
		nn=randint(0,len(pk)-1)
		if nn not in pkn:
			pkn+=[nn]			
	#print(pkn)
	pkn=vector([pk[i] for i in pkn])
	
	D=DmatrixMH(pkn)
	L=D.LLL()
	
	K=L[:L.nrows()-1].right_kernel()
	KM=K.matrix().echelon_form()
	rtv=KM.solve_left(pkn)	
	r2=rtv[0]
	t2=abs(rtv[1])
	g=xgcd(r2,t2)
	h2=-abs(g[1])		
	return(h2,t2,KM,pkn)

def indexer(pki,pkF):
	an=[]
	for i in pki:
		an+=[list(pkF).index(i)]
	return(an)	

def sixtest(KM,pk):
	XM=[]
	for i in range(6):
		K1=copy(KM[0])
		K2=copy(KM[1])
		K1[0]=KM[0][i]
		K1[i]=KM[0][0]
		K2[0]=KM[1][i]
		K2[i]=KM[0][0]
		pkm=copy(pk)
		pkm[i]=pk[0]
		pkm[0]=pk[i]
		XM+=[[matrix(ZZ,[K1,K2]).echelon_form(),vector(pkm)]]
	return(XM)
	
def LRAMHS(pk,d):
	pkT=copy(pk)
	timestart=time.time()
	FailVal=True
	ctrR2=0
	vaI=pk
	tt2=1
	FCheck=False
	while FailVal:
		ctrR2+=1
		pkLL=[]	
		for i in range(len(vaI)):
			if vaI[i]>(tt2/2):
				FailVal=True
				pkLL+=[pk[i]]
		if len(pkLL)<=d:
			pkLL+=pk[:d-len(pkLL)]
		#	print(indexer(pkLL,pk))
			FailVal=False
		if FailVal:	
			Y=LRAInter(vector(pkLL),d)
				
			hh2=Y[0]
			tt2=abs(Y[1])
			vaI=hh2*vector(pkLL)%tt2
	
	timenext=time.time()-timestart
	A=PTest(pkLL,pk,6)
	return(A[0]+timenext,A[1],A[2]+ctrR2)


def LRAMHSc(pk,d):
	pkT=copy(pk)
	timestart=time.time()
	FailVal=True
	ctrR2=0
	vaI=pk
	tt2=1
	FCheck=False
	while FailVal:
		ctrR2+=1
		pkLL=[]	
		for i in range(len(vaI)):
			if vaI[i]>(tt2/2):
				FailVal=True
				pkLL+=[pk[i]]
		if len(pkLL)<d:
			FailVal=False
		if FailVal:	
			Y=LRAInter(vector(pkLL),d)
				
			hh2=Y[0]
			tt2=abs(Y[1])
			vaI=hh2*vector(pkLL)%tt2
	
	FAX=hh2*pk%tt2
	SISFd=SIS(FAX[d:])
	SUMFd=(0<sum(FAX[d:])<tt2)
			
	if SUMFd and SISFd:
		timefinish=time.time()-timestart
		return(timefinish,True,ctrR2)
	else:
		timefinish=time.time()-timestart
		return(timefinish,False,0)



def PTest(pk,pkf,d):
	timestart=time.time()
	P=[[0,1,2,3,4,5],[1,2,3,4,5,0],[2,3,4,5,0,1],[3,4,5,0,1,2],[4,5,0,1,2,3],[5,0,1,2,3,4]]
	ctr=0
	for pi in P:
		ctr+=1
		pkp=MPp(pk,pi)
		fa=LRAF(pkp)
		hh2=fa[0]
		tt2=fa[1]
		FAX=hh2*pkf%tt2 
		SISFd=SIS(FAX)
		SUMFd=(0<sum(FAX)<tt2)
		if SUMFd and SISFd:
			timefinish=time.time()-timestart
			return(timefinish,True,ctr)
	timefinish=time.time()-timestart
	return(timefinish,False,0)
		
	
def PxTest(pk,pkf,d):
	timestart=time.time()
	P=Permutations(range(d))
	P=list(P)
	shuffle(P)
	ctr=0
	for pi in P[:5]:
		ctr+=1
		pkp=MPp(pk,pi)
		fa=LRAF(pkp)
		hh2=fa[0]
		tt2=fa[1]
		FAX=hh2*pkf%tt2 
		SISFd=SIS(FAX[d:])
		SUMFd=(0<sum(FAX[d:])<tt2)
		if SUMFd and SISFd:
			timefinish=time.time()-timestart
			return(timefinish,True,ctr)
	timefinish=time.time()-timestart
	return(timefinish,False,0)


def PSTest(pk,pkf,d):
	timestart=time.time()
	ctr=0
	pkp=copy(pk)
	while ctr<5:	
		shuffle(pkp)
		fa=LRAF(pkp)
		hh2=fa[0]
		tt2=fa[1]
		FAX=hh2*pkf%tt2 
		SISF=SIS(FAX)
		SISFd=SIS(FAX[d:])
		SUMF=(0<sum(FAX)<tt2)
		SUMFd=(0<sum(FAX[d:])<tt2)
		if SUMFd and SISFd:
			timefinish=time.time()-timestart
			return(timefinish,True)
		
	timefinish=time.time()-timestart
	return(timefinish,False)


			
def MerkSLRAMass(ntests,n,d):
	
	totsuccess=0
	totfail=0
	totStime=0
	totFtime=0
	permctr=0
	for i in range(ntests):
		pk=pkMH(n)
		X=LRAMHS(pk[0],d)
		if X[1]:
			totsuccess+=1
			totStime+=X[0]
			permctr+=X[2]
		else:
			totfail+=1
			totFtime+=X[0]
	print("LRA of degree",d,"succeeded against Shuffled Merkle-Hellman degree",n)
	print("with success ratio",RR(totsuccess/ntests))
	if totsuccess!=0:
		print("and average time",RR(totStime/totsuccess))
	
		print("and average LLL executions",RR(permctr/totsuccess))
	if totfail!=0:
		print("Failures have average time",RR(totFtime/totfail))	


def Mf(n,d):
	suc=True
	while suc:
		PK=pkMH(n)
		Xy=Lf(PK,d)
		suc=Xy[0]	
		if not suc:
			print(Lf(PK,d))
			return(PK,Xy[1:])
			
def SMHtest(pk,sk,de):
	v=[]
	sv=[]
	ind=[]
	for i in range(de):
		j=randint(0,len(pk)-1)
		ind+=[j]
		v+=[pk[j]]
		sv+=[sk[j]]
	D=DmatrixMH(v)
	L=D.LLL()
	return(L,D,vector(v),vector(sv),ind)	
	

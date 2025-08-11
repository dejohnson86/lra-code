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

def LRAMHUinter(pk,d):
	pkn=pk[:d]
	D=DmatrixMH(pkn)
	L=D.LLL()
	K=L[:L.nrows()-1].right_kernel().matrix()
	E=matrix(ZZ,K).echelon_form()
	rtv=E.solve_left(pkn)
	r2=rtv[0]
	t2=abs(rtv[1])
	g=xgcd(r2,t2)
	h2=g[1]
	va=h2*pk%t2
	return(va,t2,h2,E)

def MReorg(E,pkv):
	E=E.echelon_form()
	E1=SV(E[0])
	pks=vector([pkv[E1[i][1]] for i in range(len(pkv))])
	e1=vector([E[0][E1[i][1]] for i in range(len(pkv))])
	e2=vector([E[1][E1[i][1]] for i in range(len(pkv))])
	E=matrix(ZZ,[e1,e2])
	return(E.echelon_form(),pks)


def LRAInter(pk,d):
	pkn=[]
	while len(pkn)<d:
		nn=randint(0,len(pk)-1)
		if nn not in pkn:
			pkn+=[nn]			
	print(pkn)
	pkn=vector([pk[i] for i in pkn])
	
	D=DmatrixMH(pkn)
	L=D.LLL()
	
	K=L[:L.nrows()-1].right_kernel()
	KM=K.matrix()
	E2=MReorg(KM,pkn)
	rtv=E2[0].solve_left(E2[1])	
	r2=rtv[0]
	t2=abs(rtv[1])
	g=xgcd(r2,t2)
	h2=g[1]		
	return(h2,t2)

def sixtest(KM):
	XM=[]
	for i in range(6):
		K1=copy(KM[0])
		K2=copy(KM[1])
		K1[0]=KM[0][i]
		K1[i]=KM[0][0]
		K2[0]=KM[1][i]
		K2[i]=KM[0][0]
		XM+=[matrix(ZZ,[K1,K2]).echelon_form()]
	return(XM)
	
def LRAMHS(pk,sk,d):
	timestart=time.time()
	rnk=0
	ctrR1=0
	ln=0
	LN=len(pk)
	LNg=ceil(3*log(log(LN,2),2))
	
	while ln<LNg:
		ctrR1+=1
		pkn=[]
		
		while len(pkn)<d:
			nn=randint(0,len(pk)-1)
			if nn not in pkn:
				pkn+=[nn]
		skn=vector([sk[i] for i in pkn])
		pkn=vector([pk[i] for i in pkn])
		
		D=DmatrixMH(pkn)
		L=D.LLL()
		ln=l2(L[-1])-l2(L[-2])
	E=L[:L.nrows()-1].right_kernel().matrix()
	rtv=E.solve_left(pkn)
	rr2=rtv[0]
	tt2=abs(rtv[1])
	ind=0
	g=xgcd(rr2,tt2)
	hh2=-abs(g[1])
	vaI=hh2*pk%tt2
	FAX=copy(vaI)
	FailVal=True
	ctrR2=0
	while FailVal:
		ctrR2+=1
		pkLL=[]	
		FailVal=False
		for i in range(len(vaI)):
			if vaI[i]>(tt2/2):
				FailVal=True
				pkLL+=[pk[i]]
		if len(pkLL)<=6:
			pkLL+=vaI[:6-len(pkLL)]
		
		Y=LRAInter(vector(pkLL),d)	
		
		hh2=-abs(Y[0])
		tt2=abs(Y[1])
		if FailVal==False:
			break
		
		vaI=hh2*vector(pkLL)%tt2
		FAX=hh2*pk%tt2
		SISF=SIS(FAX[5:])
		SUMF=(0<sum(FAX[5:])<tt2)
		if SISF and SUMF:
			timefinish=time.time()-timestart
			return(timefinish,ctrR1,ctrR2)
		
		
	SISF=SIS(FAX)
	SISF5=SIS(FAX[5:])
	SUMF=(0<sum(FAX)<tt2)
	SUMF5=(0<sum(FAX[5:])<tt2)
	timefinish=time.time()-timestart
	return(SISF,SISF5,SUMF,SUMF5,timefinish,ctrR1,ctrR2,FAX[:15])	
			
			
def MerkSLRAMass(ntests,n,d):
	
	totsuccess=0
	tottime=0
	for i in range(ntests):
		pk=pkMHS(n)
		X=LRAMHS(pk[0],d)
		if X[0]:
			totsuccess+=1
		tottime+=X[1]
	print("LRA of degree",d,"succeeded against Shuffled Merkle-Hellman degree",n)
	print("with success ratio",RR(totsuccess/ntests))
	print("and average time",RR(tottime/ntests))	


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
	

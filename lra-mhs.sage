import time

#################################################
## Auxiliary Functions
##

# Returns bit-length of the given number
def l2(n):
	m=log(abs(n),2)
	return(RR(m))

# Tests to see if vector 'vv' represents a super-increasing sequence 
def SIS(vv):
	for i in range(2,len(vv)):
		if sum(vv[:i])>=vv[i]:
			return(False)
	return(True)

# Sorts a vector into linear order while keeping track of initial ordering 
def SV(vv):
	va=[]
	for i in range(len(vv)):
		va+=[(vv[i],i)]
	return(sorted(va))	

########
## Unshuffled Merkle-Hellman Public Key Generator
##

def kMHU(n):
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
	
	return(pk,a,W,M)	
	
########
## Shuffled Merkle-Hellman Public Key Generator
##

def kMHS(n):
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
	
####################
## LRA versus Shuffled Merkle-Hellman 
##

# Works on -unshuffled- MH public keys with n coefficients and discriminator matrix degree d; unshuffled keys are used for simplicity 
# of presentation and study, but the algorithm uses completely random internal coefficient selection so that this has no effect
# upon its success or failure
def LRAMHS(pk,d,retval):
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
			FailVal=False
		if FailVal:	
			Y=LRAInter(vector(pkLL),d)
				
			hh2=Y[0]
			tt2=abs(Y[1])
			vaI=hh2*vector(pkLL)%tt2
	
	timenext=time.time()-timestart
	A=PTest(pkLL,pk,6,retval)
	if retval:
		return(A[0]+timenext,A[1],A[2]+ctrR2,A[3])
	else:	
		return(A[0]+timenext,A[1],A[2]+ctrR2)


# Internal LRA algorithm, executed multiple times
def LRAInter(pk,d):
	pkn=[]
	while len(pkn)<d:
		nn=randint(0,len(pk)-1)
		if nn not in pkn:
			pkn+=[nn]			

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

# Final reduction of the public key using a maximum of 6 permutations of final 6 key components, one
# for each distinct possible first coefficient. Set 'retval' true to return the equivalent secret key
def PTest(pk,pkf,d,retval):
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
			if retval:
				return(timefinish,True,ctr,[FAX,hh2,tt2])
			else:
				return(timefinish,True,ctr)
	timefinish=time.time()-timestart
	return(timefinish,False,0,[0,0,0])

# Returns a vector of coefficients 'pke' given some specified permutation 'pe'  
def MPp(pkV,pe):
	pke=vector([pkV[i] for i in pe])
	return(pke)

# Internal, final execution of the LRA as sub-algorithm within 'PTest' as above
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

		
####################
## LRA versus Shuffled Merkle-Hellman Mass Testing Version 
##			

# Again, we use -unshuffled- keys for simplicity of programming, though this does not affect success or failure
# given with how the LRAMHS always uses a random draw of internal coefficients

def MerkSLRAMass(ntests,n,d):
	totsuccess=0
	totfail=0
	totStime=0
	totFtime=0
	permctr=0
	for i in range(ntests):
		pk=kMHU(n)
		X=LRAMHS(pk[0],d,False)
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

	

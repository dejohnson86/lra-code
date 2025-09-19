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


# Decryption of ciphertext 'c' for Merkle-Hellman using equivalent secret key 'esk', 
# equivalent modular inverse 'ri', equivalent modulus 't'
def mhdecr(esk,ri,t,c):
	cr=ri*c%t
	mi=zero_vector(len(esk))
	for i in range(len(esk)-1,-1,-1):
		if (cr>esk[i]):
			mi[i]=1
			cr=cr-esk[i]
	return(mi)	

# Random binary message generation of length 'n'
def mhmess(n):
	me=vector(ZZ,[randint(0,1) for i in range(n)])
	return(me)	
	
# Private key equivalence check; input public key 'pk' and equivalent (Unshuffled) secret key 'esk'
def pkeqMH(pk,esk):
	mes=mhmess(len(pk))
	print("A randomly generated plaintext is binary vector:")
	print(mes)
	
	ci=pk*mes
	print("The corresponding ciphertext is the integer:")
	print(ci)
	
	mesesk=mhdecr(esk[0],esk[1],esk[2],ci)
	print("The ciphertext as decrypted by the LRA's equivalent key is binary vector:")
	print(mesesk)
	print("And the difference between the plaintext recovered with assistance by the LRA and the original is:")
	print(mesesk-mes)	

########
## Unshuffled Merkle-Hellman Key Generator
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
## Shuffled Merkle-Hellman Key Generator
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

# Overall function to compute discriminator matrix; a more efficient implementation
# that only checks i+1, i+2, and i+3 for any given i in internal loop
def DmatrixMH(pkL):
	rl=[]
	D2=[]
	lr=len(pkL)
	LY=xgcdList(pkL)
	ln=len(LY)
	for i in range(ln-3):
		for j in range(i+1,i+4):
			if LY[i][2][0]==LY[j][2][0]:
				rl+=[eqsm(LY[i],LY[j],lr)]
					
			else:
				X1=LY[j][2][0]*vector(ZZ,LY[i][2])
				X2=LY[i][2][0]*vector(ZZ,LY[j][2])
				L1M=LY[i][:2]+[X1]
				L2M=LY[j][:2]+[X2]
				rl+=[eqsm(L1M,L2M,lr)]
		
	D=matrix(rl)
	D=D.echelon_form()
	D=D[:D.rank()]
	return(D)

# Computes the Bezout coefficients from either public polynomial with relevant indexing information	
def xgcdList(LP):
	coll=[]
	lr=len(LP)
	for i in range(lr-1):
		for j in range(i+1,lr):
			coll+=[[i,j,xgcd(LP[i],LP[j])]]
	return(coll)
	
# Using two lists of paired Bezout coefficients derived from public polynomial coefficients, 
# computes a vector in the set \mathcal{N} to be used in the discriminator matrix.
def eqsm(L1,L2,lr):
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
# upon its success or failure. Set parameter 'retval' as 'True' to include the equivalent secret key as first coefficient of final
# output.
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
		return(A[3],A[0]+timenext,A[1],A[2]+ctrR2)
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

# Returns a vector permuting coefficients of 'pkV' given some specified permutation 'pe'  
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
	if E[0][5]>t2/2:
		return(-h2,t2)
	
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

	

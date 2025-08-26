import time

#################################################
## Auxiliary Functions
##

# Returns bit-length of the given number
def l2(n):
	m=log(abs(n),2)
	return(RR(m))

# Checks if the vector is a super-increasing sequence 
def SIS(vv):
	for i in range(2,len(vv)):
		if sum(vv[:i])>=vv[i]:
			return(False)
	return(True)


def MC(vv,mr):
	for i in range(len(vv)):
		vv[i]=Mod(vv[i],mr).lift_centered()
	return(vv)	

def mhdecr(sv,ri,t,c):
	cr=ri*c%t
	mi=zero_vector(len(sv))
	for i in range(len(sv)-1,-1,-1):
		if (cr>sv[i]):
			mi[i]=1
			cr=cr-sv[i]
	return(mi)		


#################################################
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
	
	
####################################################
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

############################
## LRA-MHU Single Execution using d coefficients of the public key
##

def LRAMHU(pk,d,retval):
	timestart=time.time()
	pkn=pk[:d]
	D=DmatrixMH(pkn)
	L=D.LLL()
	K=L[:L.nrows()-1].right_kernel().matrix()
	E=K.echelon_form()
	rtv=E.solve_left(pkn)
	r2=rtv[0]
	t2=abs(rtv[1])
	ind=0
	g=xgcd(r2,t2)
	h2=g[1]
	va=h2*pk%t2
	
	timefinish=time.time()-timestart
	
	successSum=(0<sum(va)<t2)
	successSIS=SIS(va)
	success=(successSIS and successSum)
	if retval:
		return([va,h2,t2],success,timefinish)
	else:
		return(success,timefinish)	
			
	
############################
## LRA-MHU Mass Tester on public keys with n coefficients and discriminator matrix degree d
##

def MerkULRAMass(ntests,n,d):	
	totsuccess=0
	tottime=0
	for i in range(ntests):
		pk=kMHU(n)
		X=LRAMHU(pk[0],d,False)
		if X[0]:
			totsuccess+=1
		tottime+=X[1]
	print("LRA of degree",d,"succeeded against Merkle-Hellman degree",n)
	print("with success ratio",RR(totsuccess/ntests))
	print("and average time",RR(tottime/ntests))	
	
############################
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

############################
## Efficient Polynomial Time Attack Mass Simulator
##

def EPTAMass(ntests,n,d):
	tottime=0
	for i in range(ntests):
		pk=kMHU(n)[0]	
		tottime+=EPTAS(pk,d)
	
	print("EPTA of degree",d,"against Merkle-Hellman degree",n)
	print("has average time",RR(tottime/ntests))	

			
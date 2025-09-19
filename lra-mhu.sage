import time

#################################################
## Auxiliary Functions
##

# Returns bit-length of the given number
def l2(n):
	m=log(abs(n),2)
	return(RR(m))

# Checks if the vector 'vv' is a super-increasing sequence 
def SIS(vv):
	for i in range(2,len(vv)):
		if sum(vv[:i])>=vv[i]:
			return(False)
	return(True)

# Checks if the vector 'vv' is a super-increasing sequence past the m-th coefficient	
def SISm(vv,m):
	vc=copy(vv)
	vc=vc[m:]
	for i in range(2,len(vc)):
		if sum(vc[:i])>=vc[i]:
			return(False)
	return(True)	

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
	
# Private key equivalence check; input public key 'pk' and equivalent secret key 'esk'
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

# Subtracts a particular value 'va' from every entry of vector 've'
def valsubvec(ve,va):
	an=[]
	for i in ve:
		an+=[i-va]
	an=vector(an)
	return(an)	

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

# Overall function to compute discriminator matrix; a more efficient implementation
# that only checks between i+1,i+2, and i+3 for any given i
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

############################
## LRA-MHU Single Execution using d coefficients of the public key
##

# Set parameter 'retval' as 'True' to include the equivalent secret key as first coefficient of final output
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
	negval=1
	if va[10]>t2/2:
		negval=-1
		va=-valsubvec(va[10:],t2)	
		va=vector([0 for i in range(10)]+list(va))	
	timefinish=time.time()-timestart
	successSIS=SISm(va,10)
	successSum=(0<sum(va)<t2)
	
	success=(successSIS and successSum)
	if retval:
		return([va,negval*h2,t2],success,timefinish)
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

			
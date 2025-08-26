import time

'''
A selection of usable primes of the given bit-length; around 22 bits the WLRA begins to become unwieldly
so we leave such values for the simulator. The simulator sometimes encounters errors for low bit-lengths (around 16 bits). 

8 bit prime: 1009
16:50021
17:100043
18:200033
19:400067
20:800077
21:1600069
22:3200069
23:6400099
24: 16242781
32: 3320833723
40: 664171379159
48: 242034181288351
56: 54321663379688053
64: 17455010336788539313
72: 4681074808958153331041
80: 1012454528148273429462127
88: 299975996418237395409001073
120: 1044487397290507550271699514880268083
128: 188718274930580309272124860900705715969
136: 60475045147803217722699504640873937294951
174: 23639474998292043714787719276401511591355325698674617
'''
#####################################
### Universal HPPK Parameters/Objects

# default 19-bit prime
p=50021

rLL=2^6*p

sqrp=ceil((2*p)^(1/2))
l2p=ceil(log(p,2))

Z.<z>=PolynomialRing(GF(p))
X.<x>=PolynomialRing(ZZ)

md=2*ceil(log(p,2))+6
tLL=2**md
tUL=2*tLL
rLL=floor(tLL/p)

#####################################
### Auxiliary Functions

# Checks bit-length
def l2(n):
	m=log(abs(n),2)
	return(RR(m))

# Generates a random polynomial over GF(p) with degree 'degr' 
def rply(degr):
	ply=0
	for i in range(degr+1):
		ply=ply+randint(2,p-1)*z**i
	return(ply)

# Encrypts a list of integers by invertible modular multiplication	
def EL(ly,Rx,tx):
	ly2=[]
	for i in range(len(ly)):
		ly2+=[Rx*ly[i]%tx]
	return(ly2)

# Finds the number 'k' such that 'R1*n mod T1 = R1*n - T1*k'
def mtr(n,R1,T1):
	return((R1*n-(R1*n)%T1)/T1)

# Divides out the overall gcd of a vector over ZZ
def gcdoutV(vec):
	cv=gcd(vec)
	vnew=vector(ZZ,copy(vec)/cv)
	return(vnew,cv)

# Two-row matrix version of the above
def gcdoutM(mat):
	mnew=matrix(ZZ,[gcdoutV(mat[0])[0],gcdoutV(mat[1])[0]])	
	return(mnew)

# Checks if vector has elements within proper limits
def coefflims(vec):
	for i in range(6):
		if (vec[i]<1) or (vec[i]>p-1):
			return(False)
	return(True)


# Checks if degree 5 univarite polynomial can factor as needed for HPPK and the WLRA
def doesfactor(ply):
	ply=Z(ply)
	py1=ply[:3]
	py2=Z(list(ply)[3:])
	gcf=gcd(py1,py2)
	if gcf.degree()<1:
		return(False,1)		
	else:
		return(True,gcf)

# Returns the minimal equivalent integer matrix in echelon form. 
# (Minimal with respect to coefficient sizes; equivalent over QQ.)				
def MinMatrix(MT):
	mat=copy(gcdoutM(matrix(ZZ,MT).echelon_form()).echelon_form())
	mat=gcdoutM(mat)
	pv=mat[0][0]
	if pv!=1:
		FL=factor(pv)	
		for F in FL:
			for ex in range(F[1]):
				pinv=0
				f=F[0]^(ex+1)
				for j in range(1,6):
					g=xgcd(mat[1][j],f)		
					if g[0]==1:
						pinv=g[1]%f
						if pinv!=0:
							pinv=(-mat[0][j]*pinv)%f
							break
				if pinv!=0:
					isfact=True
					for j in range(1,6):
						if not f.divides(mat[0][j]+pinv*mat[1][j]):
							isfact=False
					if isfact:
						mat[0]=(mat[0]+pinv*mat[1])/f
						
	return(matrix(ZZ,mat))	

# vector setup function for the WLRA which ouputs (0,0,0,0,i1,i2) in ZZ^6
def v56(i1,i2):
	z56=zero_vector(6)
	z56[-2]=i1
	z56[-1]=i2
	return(z56)	

#####################################
### Encryption and Decryption

# Evaluates the integer polynomial 'Py' at Lxy=[x,y1,y2]	
def eval(Py,Lxy):
	ans=0
	aL=[]	
	for j in range(1,3):	
		for i in range(3):
			aL+=[(Lxy[0]^i)*Lxy[j]%p]	
	for i in range(6):
		ans+=Py[i]*aL[i]
	return(ans)
						
# Computes the ciphertext 'C' for two HPPK polynomials 'Py1' and 'Py2' at Lxy=[x,y1,y2]
def encryptHPPK(Py1,Py2,Lxy):
	C=[]
	C+=[eval(Py1,Lxy)]
	C+=[eval(Py2,Lxy)]
	return(C)	

# Decrypts the ciphertext 'C' from secret polynomials 'sp1' and 'sp2' when 
# using inverse modular values 'ri1' and 'ri2' with respective moduli 't1' and 't2'	
def decryptHPPK(C,sp1,sp2,ri1,ri2,t1,t2):
	r1=ri1*C[0]%t1
	r2=ri2*C[1]%t2
	fp=sp1-GF(p)(r1/r2)*sp2
	m=fp.roots()[0]
	return(m)

#####################################
### Key Generation

# Generates a full HPPK secret/public key-pair '(sk,pk)', parsed as secret polynomials 'skp', public key 'pk' 
# and secret modular coefficients 'skmc'
	
def skpkgen():

	t=randint(tLL,tUL)
	q=randint(tLL,tUL)
	
	f=rply(1)
	h=rply(1)

	B=[rply(1),rply(1)]

	P=[X(f*b) for b in B]
	Q=[X(h*b) for b in B]

	Ps=P[0].coefficients(sparse=False)+P[1].coefficients(sparse=False)
	Qs=Q[0].coefficients(sparse=False)+Q[1].coefficients(sparse=False)
	
	Pmin=min(Ps)
	Qmin=min(Qs)
	rLL=ceil(t/Pmin)
	SLL=ceil(q/Qmin)

	R=0
	while (gcd(R,t)!=1):	
		R=randint(rLL,t)
	S=0
	while (gcd(S,q)!=1):	
		S=randint(SLL,q)
		
	Ri=xgcd(R,t)[1]%t
	Si=xgcd(S,q)[1]%q

	vPs=vector(Ps)
	vQs=vector(Qs)

	ZP=Z(list(vPs))
	ZQ=Z(list(vQs))

	Pp=EL(Ps,R,t)
	Qp=EL(Qs,S,q)
	Pp=vector(ZZ,Pp)
	Qp=vector(ZZ,Qp)

	skp=[Ps,Qs]
	pk=[Pp,Qp]
	skmc=[[t,R,Ri],[q,S,Si]]
	return(skp,pk,skmc)


#####################################
### Discriminator Matrix

# Builds the discriminator matrix from a list of public polynomial coefficients
def discriminator(pkL):
	rl=[]
	D2=[]
	LY=xgcdList(pkL)
	ln=len(LY)
	for i in range(ln):
		for j in range(i+1,ln):
			if LY[i][2][0]==LY[j][2][0]:
				rl+=[eqsm(LY[i],LY[j])]				
			else:
				X1=LY[j][2][0]*vector(ZZ,LY[i][2])
				X2=LY[i][2][0]*vector(ZZ,LY[j][2])
				L1M=LY[i][:2]+[X1]
				L2M=LY[j][:2]+[X2]
				rl+=[eqsm(L1M,L2M)]
	D=matrix(rl)
	D=D.echelon_form()
	D=D[:D.rank()]
	return(D)

# Computes the xgcd/Bezout coefficients for pairs of public key elements in the list 'LP' 
def xgcdList(LP):
	coll=[]
	for i in range(5):
		for j in range(i+1,6):
			coll+=[[i,j,xgcd(LP[i],LP[j])]]
	return(coll)

# Using two lists of paired Bezout coefficients derived from public polynomial coefficients, 
# computes a vector in the set \mathcal{N} to be used in the discriminator matrix.
def eqsm(L1,L2):
	fineq=[0 for i in range(6)]
	g0123=[L1[2][1],L1[2][2],L2[2][1],L2[2][2]]
	for i in range(4):
		if i<2:
			fineq[L1[i]]+=g0123[i]
		else:
			fineq[L2[i%2]]-=g0123[i]
	return(fineq)

###############################################
### Weak Lattice Reconstitution Attack on HPPK
###############################################

# Overall algorithm for the WLRA; operates on HPPK public keys. Set 'diagn' as 'True' for extra diagnostic information during
# execution. Output begins with 0,1, or 2 depending on how far the algorithm gets towards success; '2' is complete success.
def WLRA(K,diagn):
	SV=0
	PK=K[1]
	
	if diagn:
		timex=time.time()
		print("Secret polynomials:")
		print(factor(Z(K[0][0])))
		print(factor(Z(K[0][1])))
	MM=[discriminator(PK[0]),discriminator(PK[1])]
	RM=[WLRAHalfStart(PK[0],diagn),WLRAHalfStart(PK[1],diagn)]
	NumSteps=[0,0]
	HTimes=[RM[0][2],RM[1][2]]
	timey=time.time()
	NumSteps[0]=RM[0][1]+RM[1][1]
	if (RM[0][0]==0) or (RM[1][0]==0):
		return(SV,NumSteps,sum(HTimes))
	else:
		SV=1
	EP=[]
	EM=[]
	DR=[]
	SS=[]
	TInd=[]
	for i in range(2):
		Me=MinMatrix(RM[i][0])
		EM+=[Me]
		Mp=[X(list(Me[0])),X(list(Me[1]))]
		EP+=[Mp]
		R1=copy(Me[1])
		for j in range(1,6):
			R1[j]=abs(R1[j])
		mdelta=ceil(p/abs(max(R1)))
		inde=list(R1).index(max(R1))
		mratio=Me[0][inde]/Me[1][inde]
		DR+=[[mdelta,mratio]]	
		TInd+=[floor((p-1)/Me[0][0])]
		SS+=[EM[i].solve_left(vector(ZZ,K[0][i]))]
	
	#Final search for secret key vector in Z_p#
	FSet=[[],[]]
	TotFail=True
	sw=0
	while (TotFail):
		xy=[False,1]
		
		while (not xy[0]) and (TInd[sw]>1):
			
			minjpar=round(TInd[sw]*DR[sw][1]-DR[sw][0]-1)			
			exply=TInd[sw]*EP[sw][0]-minjpar*EP[sw][1]		
			
			for j in range(2*DR[sw][0]+3):
				if coefflims(exply):
					retV=doesfactor(exply)

					if retV[0]:
						xy=checkT(MM[sw],vector(ZZ,exply))

						if xy[0]:
							FSet[sw]+=[Z(exply)]
							break
				exply-=EP[sw][1]
			
			if (not xy[0]) and ((TInd[sw]*EM[sw][0][0])==K[0][sw][0]):
				print("Secret poly",K[0][sw])
				print("Secret R,t",K[2][sw])
				print(EM[sw])
				print("Matrix",sw, "solves as")
				print(SS[sw])
				print("Mdelta:")
				print(DR[sw][0])
				print("Mratio:")
				print(DR[sw][1])
				print("At", TInd[sw], "checked range for 2nd coord as")
				print(minjpar,minjpar+2*DR[sw][0]+3)
				exply=TInd[sw]*EP[sw][0]-minjpar*EP[sw][1]
				for j in range(2*DR[sw][0]+3):
					print(exply)
					print(checkT(MM[sw],vector(ZZ,exply)))
					exply-=EP[sw][1]
			
			TInd[sw]=TInd[sw]-1
		if FSet[sw]==[]:
			timey=sum(HTimes)+time.time()-timey
			print("Somehow the set was empty...")
			print("Matrix",sw,":")
			print(EM[sw])
			print(SS[sw])
			print("Mdelta:")
			print(DR[sw][0])
			print("Mratio:")
			print(DR[sw][1])
			NumSteps[1]=2*(p-1-TInd[0])*DR[0][0]+2*(p-1-TInd[1])*DR[1][0]
			
			return(SV,NumSteps,timey)
		
		sw=(sw+1)%2
		Tot=CFail(FSet[0],FSet[1])
		TotFail=Tot[0]
		if (sum(TInd))<=2:
			print("What???")
			print(EM[0])
			print(SS[0])
			print(EM[1])
			print(SS[1])
			timey=sum(HTimes)+time.time()-timey
			NumSteps[1]=2*(p-1-TInd[0])*DR[0][0]+2*(p-1-TInd[1])*DR[1][0]
			return(SV,NumSteps,timey)
	NumSteps[1]=(p-1-TInd[0])*DR[0][0]+(p-1-TInd[1])*DR[1][0]
	SV=2
	timey=sum(HTimes)+time.time()-timey
	if diagn:
		print("We recovered:")
		for el in Tot[1]:
			print(factor(el))
		print("After",(time.time()-timex)/60,"mins")	
	return(SV,NumSteps,timey,K)

# Opening function of the WLRA executed on either public key polynomial P^L or P^R; set 
# 'diagn' as 'True' for extra diagnostic information during execution
def WLRAHalfStart(PK,diagn):
	timey=time.time()
	ctr=0
	Tctr=0	
	Mat=discriminator(PK)
	for i in range(sqrp-1,0,-1):
		for k in range(4):
			for j in range(sqrp-1,i-1,-1):
				ctr+=1
				if k==0:
					vexp=v56(i,j)
				elif k==1:
					vexp=v56(j,i)
				elif k==2:
					vexp=v56(i,-j)
				else:
					vexp=v56(j,-i)
				
				vM=Mat[4]*vexp

				fmax=factor(vM)[-1][0]
				if fmax<sqrp:
					continue
				vF=True
				for r in range(3,-1,-1):
					rposs=(-xgcd(fmax,Mat[r][r])[2]*(Mat[r]*vexp))%fmax
					if abs(rposs)>sqrp:					
						rposs=rposs-fmax
						if abs(rposs)>sqrp:
							vF=False
					if (vF==False):
						break
					vexp[r]=rposs
				if vF==False:
					continue
				
				compval=Mat[4]*vexp
				for r in range(4):
					compval=gcd(compval,Mat[r]*vexp)
				
				if (compval<rLL):	
					continue
				print(vexp)		
				VL=matrix(ZZ,gcdoutV(vexp)[0])

				VX=VL.stack(PK)
				
				if diagn:
					print("Took", ctr, "steps to find u^x:")
					print("Log_2 this is", log(1.0*ctr,2.0))
					print("u^x is",VL[0])	
				
				timey=time.time()-timey
				if i==0:
					return([0,0],ctr,timey)
				return(VX,ctr,timey)
	if diagn:
		print("A1 failed; no secondary vector found")
	return(0,ctr,time.time()-timey)


######################################################
### Weak Lattice Reconstitution Attack Mass Execution 
######################################################

# Algorithm for a larger executions of the WLRA with 'rounds' many randomly generated keys. Outputs statistical averages
# of relevant information; set 'diagn' to true for further output details 
def	WLRAMass(rounds,diagn):
	print("Prime number",p,"of bit length",l2p)
	TSteps1=[0,0,0]
	TSteps2=[0,0,0]
	TimeAv=[0,0,0]
	TProb=[0,0,0]
	TSucc=[0,0,0]
	
	timez=time.time()
	
	for j in range(rounds):
		key=skpkgen()
		EX=WLRA(key,diagn)
		
		TSucc[EX[0]]+=1
		TSteps1[EX[0]]+=EX[1][0]
		TSteps2[EX[0]]+=EX[1][1]
		TimeAv[EX[0]]+=EX[2]
		
		timez=time.time()-timez
		if (j%2==0):
			print("Round", j+1, "of", rounds, "done at", timez/60, "minutes")
	
	for j in range(3):
		if TSucc[j]!=0:
			TSteps1[j]=l2(TSteps1[j]/TSucc[j])
			print("Algorithm stage",j+1, "has total average steps A1 (log_2) of", TSteps1[j])
			if j>=1:
				TSteps2[j]=l2(TSteps2[j]/TSucc[j])
				print("Algorithm stage",j+1, "has total average steps A2 (log_2) of", TSteps2[j])		
			TimeAv[j]=RR(TimeAv[j]/TSucc[j]/60)
			print("Algorithm stage",j+1, "has total average time (min) of", TimeAv[j])
			TProb[j]=RR(TSucc[j]/rounds)			
			print("Algorithm stage",j+1, "has total average termination probability of", TProb[j])

	return(TSteps1,TSteps2,TimeAv,TSucc,TProb)
	
##############################################
#!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
### Weak Lattice Reconstitution Simulator
#!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
##############################################

#Everything to do with the simulated version

#########################################
### Key Generation + Auxiliary Functions

# Key generator for the WLRA Simulator. Given we do not check the successful dividing form of HPPK polynomials
# within the simulator (the correct answer divides as required by HPPK's construction) we create only half-keys
def skMgen():
	t=randint(tLL,tUL)
	f=rply(1)
	B=[rply(1),rply(1)]
	P=[X(f*b) for b in B]
	Ps=P[0].coefficients(sparse=False)+P[1].coefficients(sparse=False)
	Pmin=min(Ps)
	rLL=ceil(t/Pmin)
	
	R=0
	while (gcd(R,t)!=1):	
		R=randint(rLL,t)
	
	Ri=xgcd(R,t)[1]%t
	vPs=vector(Ps)
	ZP=Z(list(vPs))
	Pp=EL(Ps,R,t)
	Pp=vector(ZZ,Pp)
	bPv=vector([mtr(i,R,t) for i in Ps])	
	MP=matrix(ZZ,[vPs,bPv])
	
	return(Pp,MP,t,R,Ri)

# Nevertheless we have a function for generating two such half-keys, because the simulator must succeed 
# for a pair to succeed overall. This is used only for the "Mass" version; the 'WLRASim' uses skMGen() keys
def KGen():
	k1=skMgen()
	k2=skMgen()
	return(k1,k2)

# Function which checks if any potential value for 't' (as greater than the lower limit tLL)
# indeed could divide the given vector 'xx=mat*vec'	
def checkT(mat,vec):
	xx=vector(ZZ,mat*vec)
	cv=gcd(xx[0],xx[1])
	for i in range(2,5):
		cv=gcd(cv,xx[i])
	xx=xx/cv
	if (cv<tLL):
		return(False,cv)
	else:
		return(True,cv)

# Function defined to return 'False' and the pair of univariate polynomials '(si,sj)' if their gcd has degree 4		
def CFail(S1,S2):
	for si in S1:
		for sj in S2:
			if (gcd(si,sj).degree()==4):
				return(False,[si,sj])	
	return(True,[1,1])		

# Function which checks if the given vector dot product (the 5th row of 'mat' with 'vec') has a factor
# greater than 2*sqrt(p)
def check(mat,vec):
	vM=mat[4]*vec
	fmax=factor(vM)[-1][0]
	if fmax<sqrp:
		return(False,fmax)
	else:
		return(True,fmax)	

# Function which checks if the given vector has a gcd greater than the
# absolute minimum possible value for secret modular constant 'r'

def checkR(mat,vec):
	xx=vector(ZZ,mat*vec)
	cv=gcd(xx)
	if (cv<rLL):
		return(False,cv)
	else:
		return(True,cv)


#########################################
### Overall algorithm for WLRA-HPPK-Sim
 
def WLRASim(K):
	SV=0
	TC=WLRAHalfFake(K)
	if TC[0]:
		EM=MinMatrix(K[1])
		cpair=EM.solve_left(vector(ZZ,K[1][0]))		
		mdelta=ceil(p/abs(max(EM[1])))	
		inde=list(EM[1]).index(max(EM[1]))
		mratio=abs(EM[0][inde]/EM[1][inde])
		
		minjpar=round(K[1][0][0]/EM[0][0]*mratio-mdelta)	
		maxjpar=minjpar+mdelta
		
		if minjpar<=abs(cpair[1])<=maxjpar:
			A2s=mdelta*floor((p-1-K[1][0][0])/EM[0][0])
			return(2,TC[1],A2s)
		else:
			print(EM)
			print(mdelta)
			print(mratio)
			print("Checking",(minjpar,maxjpar))
			print("For",cpair)
			return(1,TC[1],p*mdelta)
	else:
		return(0,TC[1],0)



# Half the execution of the WLRA Simulator
def WLRAHalfFake(K):	
	ctr=0
	Cases=[]
	PM=discriminator(K[0])
	M=K[1].LLL()
	gl=floor(l2p/2)
	for i in range(gl):	
		for j in range(gl):
			for k in range(2):
				ctr+=1
				if k==0:								
					vexp=vector(ZZ,[i,j])
				else:
					vexp=vector(ZZ,[i,-j])
				
				vtry=vexp*M
				a1=abs(vtry[-1])
				a2=abs(vtry[-2])
				vtry*=sign(vtry[0])
				if (0<a1<sqrp) and (0<a2<sqrp):
					if vtry not in Cases:
						Cases+=[vtry]
	Cases=list(reversed(Cases))
	for v in Cases:
		c1=check(PM,v)
		if c1[0]:
			c2=checkR(PM,v)
			if c2[0]:
				steps=4*(sqrp-abs(v[-1]))*(sqrp-abs(v[-2]))
				return(True,steps,v)
	return(False,2*p,zero_vector(6))				



#########################################
### Mass execution of WLRA Simulator

def	WLRASimMass(rounds):
	print("Prime number",p,"of bit length",l2p)
	TSteps1=0
	TSteps2=0
	TProb=0
	TSucc=0
	
	timez=time.time()
	
	for j in range(rounds):
		key=KGen()
		EX=[0,0,0]
		for i in range(2):
			ex=WLRASim(key[i])
			for j in range(3):
				EX[j]+=ex[j]
		if EX[0]==4:
			TSucc+=1
			TSteps1+=EX[1]
			TSteps2+=EX[2]
		
		timez=time.time()-timez
		if ((j%20)==0):
			print("Round", j+1, "of", rounds, "done at", timez/60, "minutes")
	if TSucc!=0:
		TSteps1=l2(TSteps1/(2*TSucc))
		print("Succeeding LRA has total average steps A1 (log_2) of", TSteps1)
		TSteps2=l2(TSteps2/(2*TSucc))
		print("Succeeding LRA has total average steps A2 (log_2) of", TSteps2)		
	TProb=RR(TSucc/rounds)			
	print("LRA has averaged success probability of", TProb)
	return(TSucc,TSteps1,TSteps2,TProb)
	

	
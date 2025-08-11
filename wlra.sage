import time
from sage.libs.libecm import ecmfactor
'''
8 bit prime: 1009
16:50021
17:100043
18:200033
19:400067
20:800077
21:1600069
22:3200069
23:6400099
24:12800071
25:25600073
26:51200099
30:819201601

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
p=3320833723

def l2(n):
	m=log(abs(n),2)
	return(RR(m))

l2p=l2(p)
sqrp=ceil((2*p)^(1/2))

Z.<z>=PolynomialRing(GF(p))
X.<x>=PolynomialRing(ZZ)

md=2*ceil(log(p,2))+8
TLL=2**md
TUL=2*TLL

AbsRLL=floor(TLL/p)


def LRAF(PK):
	TFA=[]
	for i in range(2):
		TFA+=LRAFH(PK[i])
	return(TFA)	

def LRAFH(pubk):
	PFA=[]
	D=matro(pubk)
	SR=SRoots(pubk)
	NM=SR[1]
	
	for r in SR[0]:
		PFA+=[SRecover(NM,vector(ZZ,r[1]))]
	
	FA=[]
	for ax in PFA:
		at=gcdoutV(ax[1])[0]
		tp=gcdoutV(D*at)[1]
		ind=0
		while(gcd(tp,at[ind])!=1):
			ind+=1
			
		Rp=xgcd(at[ind],tp)[1]*pubk[ind]%tp
		FK=Rp*at%tp
		if vector(ZZ,pubk)==vector(ZZ,FK):
			return(at,Rp,tp)		


def Hp(PK):
	Mat=matro(PK)
	D=Mat.LLL()
	D=D.matrix_from_rows(range(4))
	D=D.right_kernel().matrix()
	return(D)

def SRecover(EM,vf):
	Tv=[]
	for i in range(6):
		ZF=[]
		for j in range(5):
			ZF+=[randint(1,p)*vf%p]
		
		A=EM.stack(matrix(ZF))
		KAv=vector((A.left_kernel()).matrix())
		Tv+=[KAv[2:]*A[2:]]
	TV=(matrix(Tv).LLL())[4:]
	TT=copy(TV)
	TT[0]*=TT[0][0].sign()
	TT[1]*=TT[1][0].sign()
	return(TT)	
		
def SRoots(pubk):
	M=Hp(pubk)
	N=matrix(GF(p),copy(M))
	N[1]=N[1]/N[1][1]
	N[0]=N[0]/N[0][0]
	U=matricizer(N)
	Sply=plyfourth(U[0],U[1])
	rts=Sply.roots()
	Fposs=[]
	for r in rts:
		vr=vector(GF(p),[1,r[0],r[0]^2])
		mp=-vr*U[0][0]/(vr*U[1][0])
		vp=vector(GF(p),list(U[0][0]+mp*U[1][0])+list(U[0][1]+mp*U[1][1]))
		Fposs+=[[r[0],vp]]
	return(Fposs,M)
	
def matricizer(M):
	Tm=matrix(GF(p),[M[0][:3],M[0][3:]])
	Am=matrix(GF(p),[M[1][:3],M[1][3:]])
	return(Tm,Am)

def plyfourth(T,A):
	Gam=z+A[0][2]*z^2
	Bet=-1-T[0][1]*z-T[0][2]*z^2
	Phi=(T[1][0]+T[1][1]*z+T[1][2]*z^2)*Gam+Bet*(A[1][0]+A[1][1]*z+A[1][2]*z^2)
	return(Phi)

RLL=2^6*p

def LRAp(K,diag):
	SV=0
	PK=K[1]
	timex=time.time()
	HTimes=[0,0]
	if diag:
		print("Secret polynomials:")
		print(factor(Z(K[0][0])))
		print(factor(Z(K[0][1])))
	MM=[matro(PK[0]),matro(PK[1])]
	RM=[Hp(PK[0]),Hp(PK[1])]
	NumSteps=[0,0]
	timey=time.time()
	NumSteps[0]=RM[0][1]+RM[1][1]
	EP=[]
	EM=[]
	DR=[]
	SS=[]
	TInd=[]
	for i in range(2):
		Me=RM[i]
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
	if diag:
		print("We recovered:")
		for el in Tot[1]:
			print(factor(el))
		print("After",(time.time()-timex)/60,"mins")	
	return(SV,NumSteps,timey,K)
	

def stacks(R,t):
	LF=[]
	for i in range(1,p):
		LF+=[R*i%t]
	D=[[LF[0]]]
	ind=0
	for i in range(1,p-1):
		if LF[i]<D[ind][-1]:
			D+=[[LF[i]]]
			ind+=1
		else:
			D[ind]+=[LF[i]]
	return(LF,D)

def stacksT(pr):
	Fr=pr[1]/pr[0]
	print("Fraction t/R:",RR(Fr))
	Fr=ceil(Fr)
	FVs=[]
	D={}
	psqct=0
	Lp=2*l2p
	for i in range(Fr,p):
		va=pr[0]*i%pr[1]
		Lg=ceil(l2(va))
		if Lg>=Lp:
			psqct+=1
		else:
			FVs+=[i]
		if Lg not in D:
			D.update({Lg:1})
		else:
			D[Lg]+=1
	print("Have", psqct, "elements greater than p^2.")
	print("A total fraction of", RR(psqct/(p-Fr))) 
	return(D,FVs)
	
def stacksR(pr,para,Lp):
	Fr=pr[1]/pr[0]
	print("Fraction t/R:",RR(Fr))
	Fr=ceil(Fr)
	D={}
	psqct=0
	for j in range(para):
		i=randint(Fr,p)
		va=pr[0]*i%pr[1]
		Lg=ceil(l2(va))
		if Lg>=Lp:
			psqct+=1
		if Lg not in D:
			D.update({Lg:1})
		else:
			D[Lg]+=1
	print("Have", psqct, "elements at least log_2(",Lp,").")
	print("A total fraction of", RR(psqct/para)) 
	return(D)	


def rply(degr):
	ply=0
	for i in range(degr+1):
		ply=ply+randint(2,p-1)*z**i
	return(ply)


def EL(ly,Rx,tx):
	ly2=[]
	for i in range(len(ly)):
		ly2+=[Rx*ly[i]%tx]
	return(ly2)


def mtr(n,R1,T1):
	return((R1*n-(R1*n)%T1)/T1)


def Ez(MT):
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
	
def skpkgen():

	t=randint(TLL,TUL)
	q=randint(TLL,TUL)
	
	
	f=rply(1)
	h=rply(1)

	B=[rply(1),rply(1)]

	P=[X(f*b) for b in B]
	Q=[X(h*b) for b in B]

	Ps=P[0].coefficients(sparse=False)+P[1].coefficients(sparse=False)
	Qs=Q[0].coefficients(sparse=False)+Q[1].coefficients(sparse=False)
	
	Pmin=min(Ps)
	Qmin=min(Qs)
	RLL=ceil(t/Pmin)
	SLL=ceil(q/Qmin)

	R=0
	while (gcd(R,t)!=1):	
		R=randint(RLL,t)
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

	bPv=vector([mtr(i,R,t) for i in Ps])	
	bQv=vector([mtr(i,S,q) for i in Qs])

	MP=matrix(ZZ,[vPs,bPv])
	MQ=matrix(ZZ,[vQs,bQv])
	
	sk=[Ps,Qs]
	pk=[Pp,Qp]
	ck=[[t,R,Ri],[q,S,Si]]
	return(sk,pk,ck,[bPv,bQv],MP,MQ)


def Rtgen():
	K=skpkgen()
	Ri=K[-4][0][2]
	R=K[-4][0][1]
	t=K[-4][0][0]
	return(R,t,Ri)
	
def itergcd(LP):
	coll=[]
	for i in range(5):
		for j in range(i+1,6):
			coll+=[[i,j,xgcd(LP[i],LP[j])]]
	return(coll)


def eqsm(L1,L2):
	fineq=[0 for i in range(6)]
	g0123=[L1[2][1],L1[2][2],L2[2][1],L2[2][2]]
	for i in range(4):
		if i<2:
			fineq[L1[i]]+=g0123[i]
		else:
			fineq[L2[i%2]]-=g0123[i]
	return(fineq)
			
def matro(LY):
	rl=[]
	r2=[]
	LY=itergcd(LY)
	ln=len(LY)
	for i in range(ln):
		for j in range(i+1,ln):
			if LY[i][2][0]==LY[j][2][0]:
				rl+=[eqsm(LY[i],LY[j])]
	r1=matrix(rl)
	r1=r1.echelon_form()
	r1=r1[:r1.rank()]
	
	for i in range(5):
		cv=gcd(r1[i][i],r1[i][5])
		if cv>1:
			for j in range(5):	
				if r1[i][j]!=0:
					cv=gcd(cv,r1[i][j])	
		r2+=[r1[i]/cv]
	r2=matrix(ZZ,r2)
	return(r2)

	
def v56(i1,i2):
	z56=zero_vector(6)
	z56[-2]=i1
	z56[-1]=i2
	return(z56)	

def HalfsiesF(PK,thresh):
	ctr=0
	Tctr=0	
	Mat=matro(PK)
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
				compv=Mat*vexp
				compval=gcd(compv[0],compv[1])
				for r in range(2,5):
					compval=gcd(compval,compv[r])
				compv=compv/compval
				if CL5(compv):
					return(vexp,ctr)


def Halfsies(PK,diag):
	timey=time.time()
	ctr=0
	Tctr=0	
	Mat=matro(PK)
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
				
				if (compval<RLL):	
					continue
				print(vexp)		
				VL=matrix(ZZ,gcdoutV(vexp)[0])

				VX=VL.stack(PK)
				
				if diag:
					print("Took", ctr, "steps to find u^x:")
					print("Log_2 this is", log(1.0*ctr,2.0))
					print("u^x is",VL[0])	
				
				timey=time.time()-timey
				if i==0:
					return([0,0],ctr,timey)
				return(VX,ctr,timey)
	if diag:
		print("A1 failed; no secondary vector found")
	return(0,ctr,time.time()-timey)


def LRA(K,diag):
	SV=0
	PK=K[1]
	
	if diag:
		timex=time.time()
		print("Secret polynomials:")
		print(factor(Z(K[0][0])))
		print(factor(Z(K[0][1])))
	MM=[matro(PK[0]),matro(PK[1])]
	RM=[Halfsies(PK[0],diag),Halfsies(PK[1],diag)]
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
		Me=Ez(RM[i][0])
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
	if diag:
		print("We recovered:")
		for el in Tot[1]:
			print(factor(el))
		print("After",(time.time()-timex)/60,"mins")	
	return(SV,NumSteps,timey,K)
 
def	LRAMass(rounds,dia):
	print("Prime number",p,"of bit length",l2p)
	TSteps1=[0,0,0]
	TSteps2=[0,0,0]
	TimeAv=[0,0,0]
	TProb=[0,0,0]
	TSucc=[0,0,0]
	
	timez=time.time()
	
	for j in range(rounds):
		key=skpkgen()
		EX=LRA(key,dia)
		
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
	
def coefflims(vec):
	for i in range(6):
		if (vec[i]<1) or (vec[i]>p-1):
			return(False)
	return(True)

def CL5(vec):
	for i in range(5):
		ci=abs(vec[i])
		if (ci<1) or (ci>p-1):
			return(False)
	return(True)		

def doesfactor(ply):
	#Maybe this should be written over the integers for speed
	ply=Z(ply)
	py1=ply[:3]
	py2=Z(list(ply)[3:])
	gcf=gcd(py1,py2)
	if gcf.degree()<1:
		return(False,1)		
	else:
		return(True,gcf)
		

def CFail(S1,S2):
	for si in S1:
		for sj in S2:
			if (gcd(si,sj).degree()==4):
				return(False,[si,sj])	
	return(True,[1,1])
	
	
def gcdoutV(vec):
	ind=0
	while vec[ind]==0:
		ind+=1
	cv=gcd(vec[ind],vec[ind+1])
	if cv==1:
		return(vec,1)
	for i in range(ind+1,5):
		cv=gcd(cv,vec[i])
	vnew=vector(ZZ,copy(vec)/cv)
	return(vnew,cv)

def gcdoutM(mat):
	mnew=matrix(ZZ,[gcdoutV(mat[0])[0],gcdoutV(mat[1])[0]])	
	return(mnew)

def skMgen():
	t=randint(TLL,TUL)
	f=rply(1)
	B=[rply(1),rply(1)]
	P=[X(f*b) for b in B]
	Ps=P[0].coefficients(sparse=False)+P[1].coefficients(sparse=False)
	Pmin=min(Ps)
	RLL=ceil(t/Pmin)
	
	R=0
	while (gcd(R,t)!=1):	
		R=randint(RLL,t)
	
	Ri=xgcd(R,t)[1]%t
	vPs=vector(Ps)
	ZP=Z(list(vPs))
	Pp=EL(Ps,R,t)
	Pp=vector(ZZ,Pp)
	bPv=vector([mtr(i,R,t) for i in Ps])	
	MP=matrix(ZZ,[vPs,bPv])
	
	return(Pp,MP,t,R,Ri)

def threshtest(m):
	tdic={}
	for i in range(m):
		Y=skMgen()
		M=Y[1]
		MR=M.LLL()
		R=Y[3]
		t=Y[2]
		v=M.solve_left(MR[0])
		bl=ceil(l2(R*v[1]+t*v[0]))
		if bl not in tdic:
			tdic.update({bl:1})
		else:
			tdic[bl]+=1
	kk=tdic.keys()
	kk=sorted(list(kk))
	
	fdic={}
	for e in kk:
		fdic.update({e:tdic[e]})
	return(fdic)
	
def checkT(mat,vec):
	xx=vector(ZZ,mat*vec)
	cv=gcd(xx[0],xx[1])
	for i in range(2,5):
		cv=gcd(cv,xx[i])
	xx=xx/cv
	if (cv<TLL):
		return(False,cv)
	else:
		return(True,cv)

def checkval(mat,vec):
	xx=vector(ZZ,mat*vec)
	cv=gcd(xx[0],xx[1])
	for i in range(2,5):
		cv=gcd(cv,xx[i])
	xx=xx/cv
	return(cv,xx)


		
def eval(Py,Ly):
	ans=0
	aL=[]	
	for j in range(1,3):	
		for i in range(3):
			aL+=[(Ly[0]^i)*Ly[j]%p]
	print(aL)		
	for i in range(6):
		ans+=Py[i]*aL[i]
	return(ans)

def evalchk(Py,ct):	
	for i in range(1,p):
		for j in range(1,p):
			for k in range(1,p):
				ly=[i,j,k]
				if eval(Py,ly)==ct:
					print(ly)
					
def freeval(Py,Ly):
	ans=0
	aL=[]	
	for j in range(1,3):	
		for i in range(3):
			aL+=[(Ly[0]^i)*Ly[j]]
	print(aL)		
	for i in range(6):
		ans+=Py[i]*aL[i]
	return(ans)
	

	
def rd(n):
	if n<0:
		n=-rd(-n)
	else:	
		n=floor(n+1/2)
	return(n)		

def preval(Py,Ly):
	ans=0
	aL=[]	
	for j in range(1,3):	
		for i in range(3):
			aL+=[(Ly[0]^i)*Ly[j]%p]
	return(aL)

def HalfsiesFake(SK,r1,r2,ulim):	
	ctr=0
	ANS=[0,0]
	M1=matrix(ZZ,SK)
	M2=M1.matrix_from_columns(range(4,6))
	M2=M2.LLL()
	for i in range(r1,r2):	
		for j in range(r1,r2):
			for k in range(2):
				ctr+=1
				if k==0:								
					vexp=vector(ZZ,[i,j])
				else:
					vexp=vector(ZZ,[i,-j])
				
				vtry=vexp*M2
				a1=abs(vtry[0])
				a2=abs(vtry[1])
				if (a1<ulim) and (a2<ulim):
					if (a1>ANS[0]) and (a2>ANS[1]):
						ANS=[a1,a2]
	return(ANS)				

def HalfsiesFT(SK,r1,r2,ulim):	
	ctr=0
	ANS=[0,0]
	M1=matrix(ZZ,SK)
	M2=M1.matrix_from_columns(range(4,6))
	M3=M2.LLL()
	IT=M3.solve_left(M2)
	VA=zero_vector(6)
	for i in range(r1,r2):	
		for j in range(r1,r2):
			for k in range(2):
				ctr+=1
				if k==0:								
					vexp=vector(ZZ,[i,j])
				else:
					vexp=vector(ZZ,[i,-j])
				
				vtry=vexp*M3
				a1=abs(vtry[0])
				a2=abs(vtry[1])
				if (a1<ulim) and (a2<ulim):
					if (a1>ANS[0]) and (a2>ANS[1]):
						VA=vexp*IT
						ANS=[a1,a2]
	return(VA)		

def HalfsiesAvLim(n):
	avtot=vector(RR,[0,0])
	for i in range(n):
		kk=skpkgen()
		kk=[kk[0],kk[-1]]
		for j in range(2):
			anst=HalfsiesFake([kk[0][j],kk[1][j]],1,5,sqrp)
			avtot[0]+=anst[0]
			avtot[1]+=anst[1]
	return(avtot/(2*n))

def mratioq(mat):
	av=0
	for i in range(1,6):
		av+=abs(mat[0][i]/mat[1][i])/5	
	return(av)	
	
'''	
def FactorizerSim(n):
	tix=time.time()
	for i in range(n):
		kk=skpkgen()
		kk=[kk[0],kk[-1]]
		PK=kk[1]
		for j in range(2):
			Mat=matro(PK[j])
	generate random numbers/vectors in the appropriate range and treat them exactly as
	if they were the usual cases.
	start with time, end with time, divided by n
	tix=time.time()-tix

compare the experimental values of earlier tests against the simulated function
'''

simulation: calculate the average time taken for 10^6 (e.g.) steps for each algorithmic component
calculate the average success case for the first component, knowing that the second is simply (p/2)*av_time_2,
can also even factorize in particular case to find out if algorithm is successful
project attack for various upper limit values, 32-,48-, 64-, 128-, 256-bit cases.

note the possibility of c_1*lambda_1+c_2*lambda_2 vectors increases with parameter p
'''

def l2(n):
	m=log(abs(n),2)
	return(RR(m))
	

p=17455010336788539313

sqrp=ceil(p^(1/2))
s2p=ceil(sqrt(2*p))
l2p=ceil(log(p,2))

Z.<z>=PolynomialRing(GF(p))
X.<x>=PolynomialRing(ZZ)

md=2*ceil(log(p,2))+7
TLL=2**md
TUL=2*TLL


def prob():
	s=0
	for i in range(p^2,TUL):
		
		#lim=floor(TUL/i)
		pr=1
		for j in range(2,5):
			pr*=(1-1/(j*i))
		s+=(1/i)*pr
	return(s)	

AbsRLL=floor(TLL/p)


def rply(degr):
	ply=0
	for i in range(degr+1):
		ply=ply+randint(1,p-1)*z**i
	return(ply)


def EL(ly,Rx,tx):
	ly2=[]
	for i in range(len(ly)):
		ly2+=[Rx*ly[i]%tx]
	return(ly2)


def mtr(n,R1,T1):
	return((R1*n-(R1*n)%T1)/T1)


def Ez(MT):
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
	
def skpkgen():

	t=randint(TLL,TUL)
	q=randint(TLL,TUL)
	
	RLL=ceil(t/p)
	SLL=ceil(q/p)

	R=0
	while (gcd(R,t)!=1):	
		R=randint(RLL,t)
	S=0
	while (gcd(S,q)!=1):	
		S=randint(SLL,q)
	
	f=rply(1)
	h=rply(1)

	B=[rply(1),rply(1)]

	P=[X(f*b) for b in B]
	Q=[X(h*b) for b in B]

	Ps=P[0].coefficients(sparse=False)+P[1].coefficients(sparse=False)
	Qs=Q[0].coefficients(sparse=False)+Q[1].coefficients(sparse=False)
	
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

	bPv=vector([mtr(i,R,t) for i in Ps])	
	bQv=vector([mtr(i,S,q) for i in Qs])

	#MP=matrix(ZZ,[vPs,bPv])
	#MQ=matrix(ZZ,[vQs,bQv])
	
	sk=[Ps,Qs]
	pk=[Pp,Qp]
	ck=[[t,R,Ri],[q,S,Si]]
	return(sk,pk,ck,[bPv,bQv])

def KGen():

	t=randint(TLL,TUL)
	q=randint(TLL,TUL)
	
	RLL=ceil(t/p)
	SLL=ceil(q/p)

	R=0
	while (gcd(R,t)!=1):	
		R=randint(RLL,t)
	S=0
	while (gcd(S,q)!=1):	
		S=randint(SLL,q)
	
	f=rply(1)
	h=rply(1)

	B=[rply(1),rply(1)]

	P=[X(f*b) for b in B]
	Q=[X(h*b) for b in B]

	Ps=P[0].coefficients(sparse=False)+P[1].coefficients(sparse=False)
	Qs=Q[0].coefficients(sparse=False)+Q[1].coefficients(sparse=False)
	
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

	bPv=vector([mtr(i,R,t) for i in Ps])	
	bQv=vector([mtr(i,S,q) for i in Qs])

	PM=matrix(ZZ,[vPs,bPv])
	QM=matrix(ZZ,[vQs,bQv])

	return([Ps,Pp,PM],[Qs,Qp,QM])
	
	
def itergcd(LP):
	coll=[]
	for i in range(5):
		for j in range(i+1,6):
			coll+=[[i,j,xgcd(LP[i],LP[j])]]
	return(coll)


def eqsm(L1,L2):
	fineq=[0 for i in range(6)]
	g0123=[L1[2][1],L1[2][2],L2[2][1],L2[2][2]]
	for i in range(4):
		if i<2:
			fineq[L1[i]]+=g0123[i]
		else:
			fineq[L2[i%2]]-=g0123[i]
	return(fineq)
			
def matro(LY):
	rl=[]
	r2=[]
	LY=itergcd(LY)
	ln=len(LY)
	for i in range(ln):
		for j in range(i+1,ln):
			if LY[i][2][0]==LY[j][2][0]:
				rl+=[eqsm(LY[i],LY[j])]
	
	r1=matrix(rl)
	i=0
	while r1.rank()<5 and (i<6):
		
		j=0
		while (j<6) and (r1.rank()<5):	
			vi=LY[i][2][0]
			vj=LY[j][2][0]
			if vi!=vj:
				lx=lcm(vi,vj)
				LXi=LY[i][:2]+[(lx,LY[i][2][1]*lx/vi,LY[i][2][2]*lx/vi)]
				LXj=LY[j][:2]+[(lx,LY[j][2][1]*lx/vj,LY[j][2][2]*lx/vj)]
				r1.stack(vector(eqsm(LXi,LXj)))
			j+=1
		i+=1	
		
	r1=r1.echelon_form()
	r1=r1[:r1.rank()]
	
	for i in range(5):
		cv=gcd(r1[i][i],r1[i][5])
		if cv>1:
			for j in range(5):	
				if r1[i][j]!=0:
					cv=gcd(cv,r1[i][j])	
		r2+=[r1[i]/cv]
	r2=matrix(ZZ,r2)
	return(r2)

	
def v56(i1,i2):
	z56=zero_vector(6)
	z56[-2]=i1
	z56[-1]=i2
	return(z56)	

	

	
	
def gcdoutV(vec):
	ind=0
	while vec[ind]==0:
		ind+=1
	cv=gcd(vec[ind],vec[ind+1])
	if cv==1:
		return(vec)
	for i in range(ind+1,6):
		cv=gcd(cv,vec[i])
	vnew=vector(ZZ,copy(vec)/cv)
	return(vnew)

def gcdoutM(mat):
	mnew=matrix(ZZ,[gcdoutV(mat[0]),gcdoutV(mat[1])])	
	return(mnew)


def check(mat,vec):
	vM=mat[4]*vec
	fmax=factor(vM)[-1][0]
	if fmax<s2p:
		return(False,fmax)
	else:
		return(True,fmax)

psqrd=p^2
		
def checkR(mat,vec):
	xx=vector(ZZ,mat*vec)
	cv=gcd(xx[0],xx[1])
	for i in range(2,5):
		cv=gcd(cv,xx[i])
	xx=xx/cv
	if (cv<AbsRLL):
		return(False,cv)
	else:
		return(True,cv)

		
def eval(Py,Ly):
	ans=0
	aL=[]	
	for j in range(1,3):	
		for i in range(3):
			aL+=[(Ly[0]^i)*Ly[j]%p]
	print(aL)		
	for i in range(6):
		ans+=Py[i]*aL[i]
	return(ans)

def evalchk(Py,ct):	
	for i in range(1,p):
		for j in range(1,p):
			for k in range(1,p):
				ly=[i,j,k]
				if eval(Py,ly)==ct:
					print(ly)
					
def freeval(Py,Ly):
	ans=0
	aL=[]	
	for j in range(1,3):	
		for i in range(3):
			aL+=[(Ly[0]^i)*Ly[j]]
	print(aL)		
	for i in range(6):
		ans+=Py[i]*aL[i]
	return(ans)
	

	
def rd(n):
	if n<0:
		n=-rd(-n)
	else:	
		n=floor(n+1/2)
	return(n)		

def preval(Py,Ly):
	ans=0
	aL=[]	
	for j in range(1,3):	
		for i in range(3):
			aL+=[(Ly[0]^i)*Ly[j]%p]
	return(aL)
	
def	LRAsimMass(rounds):
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
			ex=LRAsim(key[i])
			for j in range(3):
				EX[j]+=ex[j]
		if EX[0]==4:
			TSucc+=1
			TSteps1+=EX[1]
			TSteps2+=EX[2]
		
		timez=time.time()-timez
		if ((j%20)==0):
			print("Round", j+1, "of", rounds, "done at", timez/60, "minutes")
	
	TSteps1=l2(TSteps1/(2*TSucc))
	print("Succeeding LRA has total average steps A1 (log_2) of", TSteps1)
	TSteps2=l2(TSteps2/(2*TSucc))
	print("Succeeding LRA has total average steps A2 (log_2) of", TSteps2)		
	TProb=RR(TSucc/rounds)			
	print("LRA has averaged success probability of", TProb)
	return(TSucc,TSteps1,TSteps2,TProb)
	



def LRAsim(K):
	SV=0
	TC=HalfsiesFake(K)
	if TC[0]:
		EM=Ez(K[2])
		cpair=EM.solve_left(vector(ZZ,K[0]))		
		mdelta=ceil(p/abs(max(EM[1])))	
		inde=list(EM[1]).index(max(EM[1]))
		mratio=abs(EM[0][inde]/EM[1][inde])
		
		minjpar=round(K[0][0]/EM[0][0]*mratio-mdelta)	
		maxjpar=minjpar+mdelta
		
		if minjpar<=abs(cpair[1])<=maxjpar:
			A2s=mdelta*floor((p-1-K[0][0])/EM[0][0])
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
	
	

def HalfsiesFake(K):	
	ctr=0
	Cases=[]
	PM=matro(K[1])
	M=K[2].LLL()
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
				if (0<a1<s2p) and (0<a2<s2p):
					if vtry not in Cases:
						Cases+=[vtry]
	Cases=list(reversed(Cases))
	for v in Cases:
		c1=check(PM,v)
		if c1[0]:
			c2=checkR(PM,v)
			if c2[0]:
				steps=4*(s2p-abs(v[-1]))*(s2p-abs(v[-2]))
				return(True,steps,v)
	return(False,2*p,zero_vector(6))				


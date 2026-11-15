import math
Z=[float(l) for l in open('/opt/NeuroSymbolicModel/formalization/RHV6Fresh/experiments/data/odlyzko_zeros1_first300.txt') if l.strip()]
D=lambda b,T: math.atan(2*T)-math.atan(T/b)
print("(a) series check")
for T in (14.134725141735,49.773832477672,236.524229665816,Z[299],1e3,1e6):
  for b in (0.4,0.2,0.45,0.7):
    d=D(b,T); a1=(b-.5)/T; a3=a1+(1/8-b**3)/(3*T**3)
    print(f"T={T:.4f} b={b} D={d:.6e} (b-1/2)/T={a1:.6e} relerr1={(d-a1)/d:.2e} with T^-3 term relerr={(d-a3)/d:.2e} window[-1/2T,1/T]=({-1/(2*T):.4e},{1/T:.4e})")
N=200000
s=bytearray([1])*(N+1); s[0]=s[1]=0
for i in range(2,int(N**.5)+1):
  if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
PR=[i for i in range(N+1) if s[i]]
print("nprimes",len(PR))
pos=lambda b,h,q:(h*math.log(q)-math.atan(h/b))/math.pi
cell=lambda x: math.ceil(x)-1
E148={(1,.4):35,(1,.2):115,(10,.4):15,(10,.2):35,(100,.4):2,(100,.2):10,(300,.4):3,(300,.2):7}
print("(b) predictions")
for j in (1,10,100,300):
  h=Z[j-1]
  for b in (.4,.2):
    d=D(b,h); naive=len(PR)*abs(d)/math.pi
    # density-weighted: sum over boundaries C_k (line grid) in [2,N] of C*(|d|/h)/log C
    k0=math.ceil((h*math.log(2)-math.atan(2*h))/math.pi); dens=0.0; k=k0
    while True:
      C=math.exp((math.atan(2*h)+k*math.pi)/h)
      if C>N: break
      dens+=C*(abs(d)/h)/math.log(C); k+=1
    # actual
    moved=sum(cell(pos(b,h,q))!=cell(pos(.5,h,q)) for q in PR)
    # fractional equidistribution check: fraction of line positions with frac' <= |d|/pi
    print(f"T_{j}={h:.3f} b={b} D/pi={d/math.pi:.6f} naive N|D|/pi={naive:.1f} density={dens:.1f} sd~{math.sqrt(naive):.1f} actual={moved} E148={E148[(j,b)]}")
# (c) shared primes M=Occ(l)=p_{n_l}, n_l=j-1 for zero j (1-indexed), within window
print("(c) M inside reading window")
cnt=0;cnt_lo=0;cnt_hi=0; mins=[]
for j in range(1,301):
  h=Z[j-1]; M=PR[j-1]
  x=pos(.5,h,M); fr=x-(math.ceil(x)-1)   # in (0,1]
  lo= fr<=1/(2*math.pi*h); hi= (1-fr)<1/(math.pi*h)
  cnt+= lo or hi; cnt_lo+=lo; cnt_hi+=hi
  mins.append(min(fr*2*math.pi*h,(1-fr)*math.pi*h))
print("M within full window:",cnt,"lower(beta<1/2 side):",cnt_lo,"upper:",cnt_hi, "expected ~", sum(1.5/(math.pi*Z[j]) for j in range(300)))
mins.sort(); print("smallest margin ratios",[round(m,3) for m in mins[:5]])
# for beta=0.4,0.2 at each l: does M change cell?
for b in (.4,.2):
  ch=sum(cell(pos(b,Z[j-1],PR[j-1]))!=cell(pos(.5,Z[j-1],PR[j-1])) for j in range(1,301))
  print("beta",b,"M changes cell on",ch,"/300; expected",sum(abs(D(b,Z[j]))/math.pi for j in range(300)))
# crossover q* for transport R(q)=1
print("(transport) crossover q*")
for (be,Te,bl,Tl) in ((0.4,Z[0],0.6,Z[0]),(0.2,Z[0],0.8,Z[0]),(0.5,Z[0],0.4,Z[1]),(0.6,Z[0],0.5,Z[1]),(0.5,Z[0],0.5,Z[1])):
  ne=math.hypot(be,Te); nl=math.hypot(bl,Tl); db=bl-be
  qs = math.exp(math.log(nl/ne)/db) if db!=0 else None
  print(be,round(Te,3),bl,round(Tl,3),"q* =",qs)

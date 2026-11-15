import math,bisect,statistics
Z=[float(l) for l in open('/opt/NeuroSymbolicModel/formalization/RHV6Fresh/experiments/data/odlyzko_zeros1_first300.txt') if l.strip()]
N=200000
s=bytearray([1])*(N+1); s[0]=s[1]=0
for i in range(2,int(N**.5)+1):
  if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
PR=[i for i in range(N+1) if s[i]]
# counted prime at C+ of cell of p_min(z_j)=PR[j] (n=j-1 -> p_{n+1}=PR[j]); can it change for some beta in (0,1)?
chg=0; ratios=[]
for j in range(1,301):
  T=Z[j-1]; q=PR[j]
  th=(T*math.log(q)-math.atan(2*T))/math.pi; k=math.ceil(th)-1
  Cp=math.exp((math.atan(2*T)+(k+1)*math.pi)/T)
  lo=Cp*math.exp(-1/T**2); hi=Cp*math.exp(1/(2*T**2))
  # primes in [lo,hi] or cell change of q
  a=bisect.bisect_left(PR,lo); b=bisect.bisect_right(PR,hi)
  fr=th-k
  cellchg = fr<=1/(2*math.pi*T) or 1-fr<1/(math.pi*T)
  if b>a or cellchg: chg+=1
print("counted prime at C+ (cell of p_min) can change for some beta in (0,1):",chg,"/300")
# size: height part of transport of M vs radial translation bound
for j in range(1,300):
  Te,Tl=Z[j-1],Z[j]; M=PR[j]
  hp=((Tl-Te)*math.log(M)-(math.atan(2*Tl)-math.atan(2*Te)))/math.pi
  ratios.append(hp/(1/(2*math.pi*Tl)))
print("height part / max radial translation (cells): median",statistics.median(ratios),"min",min(ratios))

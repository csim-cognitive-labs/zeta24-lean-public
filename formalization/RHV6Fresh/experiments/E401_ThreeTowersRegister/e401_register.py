# E401 — registre déterministe, trois Tours, 168 écarts p_n <= 1000, trois canaux + demande exacte du canal lissé.
# Usage : python3 -I e401_register.py <dps>   (30 ou 50). Borné : < 2 min.
import sys
from mpmath import mp, mpc, mpf, exp, log, atan, pi, ei, re, zeta, zetazero, ceil, floor, nsum, inf
dps = int(sys.argv[1]); mp.dps = dps
CERT = ['14.134725141734693790457251983562','21.022039638771554992628479593897','25.010857580145688763213790992563']
def primes_upto(n):
    s = bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
P = primes_upto(1100); P = P[:169]            # p_0 = 2 ... p_168 = 1009 : 168 écarts avec p_n <= 1000
assert P[167] == 997 and P[168] == 1009
# Λ(m) pour m < 1010
Lam = {}
for p in primes_upto(1100):
    q = p
    while q <= 1100: Lam[q] = log(p); q *= p
def R(x):
    x = mpf(x); S = sum(Lam[m]*(1 - mpf(m)/x) for m in Lam if m < x)
    lz0 = -(zeta(0, derivative=1)/zeta(0))
    lzm1 = zeta(-1, derivative=1)/zeta(-1)
    triv = nsum(lambda j: -(x**(-2*(j+1)))/((-2*(j+1))*(-2*(j+1)+1)), [0, inf])
    return S - (x/2 + lz0 + lzm1/x + triv)
K = 100
zeros = [zetazero(k).imag for k in range(1, K+1)]
for j in range(3):
    assert abs(zeros[j] - mpf(CERT[j])) < mpf(10)**(-28), (j, zeros[j])
rho = [mpc(mpf(1)/2, T) for T in zeros]
def raw(r,a,b): return -2*re((mpf(b)**r - mpf(a)**r)/r)
def Jc(r,a,b):  return -2*re(ei(r*log(b)) - ei(r*log(a)))
def sm(r,a,b):  return -2*re((mpf(b)**r - mpf(a)**r)/(r*(r+1)))
def contacts_in(T, a, b):
    phi = atan(T/mpf('0.5'))
    kmin = int(ceil((T*log(a) - phi)/pi)); kmax = int(floor((T*log(b) - phi)/pi))
    return [k for k in range(kmin, kmax+1) if a < exp((phi+k*pi)/T) <= b]
out = open('e401_register_dps%d.txt'%dps,'w')
out.write("# dps=%d ; colonnes : n p_n p_{n+1} | contacts T1 | T2 | T3 | brut T1 T2 T3 somme | J somme | lissé T1 T2 T3 somme | demande exacte | résidu(3) | résidu(30) | résidu(100)\n"%dps)
Rv = [R(p) for p in P]
tot = {'raw':[0,0,0],'J':[0,0,0],'sm':[0,0,0]}
maxres = {3:mpf(0),30:mpf(0),100:mpf(0)}
for n in range(168):
    a, b = P[n], P[n+1]
    cs = [contacts_in(zeros[j], a, b) for j in range(3)]
    r = [raw(rho[j],a,b) for j in range(3)]; jj=[Jc(rho[j],a,b) for j in range(3)]; s=[sm(rho[j],a,b) for j in range(3)]
    for j in range(3): tot['raw'][j]+=r[j]; tot['J'][j]+=jj[j]; tot['sm'][j]+=s[j]
    dem = Rv[n+1]-Rv[n]
    res = {k: dem - sum(sm(rho[i],a,b) for i in range(k)) for k in (3,30,100)}
    for k in res: maxres[k] = max(maxres[k], abs(res[k]))
    f = lambda v: mp.nstr(v, 12)
    out.write("%d %d %d | %s | %s | %s | %s %s %s %s | %s | %s %s %s %s | %s | %s | %s | %s\n" % (n,a,b,cs[0],cs[1],cs[2],
        f(r[0]),f(r[1]),f(r[2]),f(sum(r)), f(sum(jj)), f(s[0]),f(s[1]),f(s[2]),f(sum(s)), f(dem), f(res[3]), f(res[30]), f(res[100])))
out.close()
print("dps", dps)
print("zéros 1..3 recalculés = certifiés à 1e-28 : OK")
for j in range(3):
    print("Tour %d télescopage brut : somme écarts - [2,1009] ="%(j+1), mp.nstr(tot['raw'][j]-raw(rho[j],2,1009),5),
          "| J :", mp.nstr(tot['J'][j]-Jc(rho[j],2,1009),5), "| lissé :", mp.nstr(tot['sm'][j]-sm(rho[j],2,1009),5))
print("demande totale [2,1009] =", mp.nstr(Rv[168]-Rv[0],15))
for k in (3,30,100): print("max |demande - somme lissée des %d premiers zéros| sur les 168 écarts :"%k, mp.nstr(maxres[k],8))
print("nombre d'écarts où la somme lissée des 3 Tours égale la demande à 1e-20 :", sum(1 for n in range(168) if abs((Rv[n+1]-Rv[n]) - sum(sm(rho[i],P[n],P[n+1]) for i in range(3))) < mpf(10)**-20))

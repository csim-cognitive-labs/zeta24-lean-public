# Jumeau déterministe des nombres du texte collé : 3 premiers zéros, contacts C_k, contributions par écart
# canal brut (x^rho/rho), canal de comptage J (Ei), canal lissé (x^rho/(rho(rho+1))). mpmath 30 chiffres.
from mpmath import mp, mpc, mpf, exp, log, atan, pi, ei, re, cos
mp.dps = 30
Ts = [mpf('14.134725141734693790457251983562'), mpf('21.022039638771554992628479593897'), mpf('25.010857580145688763213790992563')]
beta = mpf('0.5')
primes = [2,3,5,7,11,13,17,19,23,29,31,37]
print("contacts C_k = exp((arg rho + k pi)/T)")
for j,T in enumerate(Ts):
    rho = mpc(beta,T); a = atan(T/beta)
    print("T%d"%(j+1), [mp.nstr(exp((a+k*pi)/T),10) for k in range(0,11)])
def raw(rho,a,b):  return -2*re((mpf(b)**rho - mpf(a)**rho)/rho)
def J(rho,a,b):    return -2*re(ei(rho*log(b)) - ei(rho*log(a)))
def sm(rho,a,b):   return -2*re((mpf(b)**rho - mpf(a)**rho)/(rho*(rho+1)))
print("gap | raw T1 T2 T3 sum | J sum | smoothed sum")
for a,b in zip(primes[:-1],primes[1:]):
    r=[raw(mpc(beta,T),a,b) for T in Ts]; jj=[J(mpc(beta,T),a,b) for T in Ts]; s=[sm(mpc(beta,T),a,b) for T in Ts]
    print("%d-%d"%(a,b), [mp.nstr(x,7) for x in r], mp.nstr(sum(r),7), "|", mp.nstr(sum(jj),7), "|", mp.nstr(sum(s),7))

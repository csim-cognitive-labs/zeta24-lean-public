#!/usr/bin/env python3
"""E457 — diagnostic des cas où la vérification directe aux bords a échoué en double précision : recalcul en précision
étendue (mpmath, 40 chiffres) de la fraction de cellule au premier limitant et des deux tests, pour chaque cas signalé."""
import sys, math
import numpy as np, mpmath as mp
mp.mp.dps = 40
ZFILE = sys.argv[1]
N = 10**6
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0].astype(np.float64); logp = np.log(primes)
heights = np.array([float(l.split()[0]) for l in open(ZFILE) if l.strip()])[:200]
def stage(beta, T): return (T * logp - math.atan(T / beta)) / math.pi
def dbeta(beta, T):
    s = stage(beta, T); f = s - np.floor(s); th = math.atan(T/beta) - math.pi*(1-f)
    c = np.full_like(s, 1-beta); pos = th > 0; c[pos] = np.minimum(T/np.tan(th[pos]) - beta, 1-beta)
    j = int(np.argmin(c)); return float(c[j]), j, np.floor(s)
def dT(beta, T):
    s = stage(beta, T); k1 = np.floor(s)+1; Tp = np.full_like(s, T)
    for _ in range(40):
        Tp = Tp - (Tp*logp - np.arctan(Tp/beta) - math.pi*k1)/(logp - beta/(beta**2+Tp**2))
    j = int(np.argmin(Tp-T)); return float(Tp[j]-T), j
def chk(fl, b2, T2): return bool(np.all(np.floor(stage(b2, T2)) == fl))
def mp_stage(beta, T, q): return (T*mp.log(q) - mp.atan(T/beta))/mp.pi
tot = 0; expl = 0
for beta in (0.5, 0.3, 0.4, 0.45):
    for T in heights:
        db, jb, fl = dbeta(beta, T); dt, jt = dT(beta, T)
        tests = {'β_in': chk(fl, beta+db*(1-1e-6), T), 'T_in': chk(fl, beta, T+dt*(1-1e-6)),
                 'β_out': (not chk(fl, beta+db*(1+1e-3), T)) if beta+db*(1+1e-3) < 1 else True,
                 'T_out': not chk(fl, beta, T+dt*(1+1e-3))}
        if all(tests.values()): continue
        tot += 1
        bad = [k for k, v in tests.items() if not v]
        # précision étendue au premier limitant de chaque marge
        qb, qt = int(primes[jb]), int(primes[jt])
        sb = mp_stage(beta, T, qb); st = mp_stage(beta, T, qt)
        gb = 1 - (sb - mp.floor(sb)); gt = 1 - (st - mp.floor(st))
        # second premier le plus limitant pour ΔT (double)
        s = stage(beta, T); g = 1 - (s - np.floor(s)); order = np.argsort(g); q2 = int(primes[order[1]]); g2 = float(g[order[1]])
        # cause : écart 1−f au premier limitant comparable au bruit double (|s|·2e-16) ou deux premiers quasi ex æquo
        noise = abs(float(sb)) * 2.2e-16
        cause = []
        if float(gb) < 1e3*noise or float(gt) < 1e3*noise: cause.append('1−f de l ordre du bruit double')
        if abs(g2 - float(gt)) / max(float(gt), 1e-300) < 2e-3: cause.append('deux premiers limitants quasi ex æquo (test « au-delà » à 10⁻³ près)')
        if cause: expl += 1
        print('β=%.2f T=%.6f échecs=%s ; premier limitant Δβ=%d (1−f=%s) ; ΔT=%d (1−f=%s) ; second premier ΔT=%d (1−f=%.3e) ; bruit double≈%.1e ; cause : %s'
              % (beta, T, bad, qb, mp.nstr(gb, 6), qt, mp.nstr(gt, 6), q2, g2, noise, ' ; '.join(cause) or 'NON EXPLIQUÉE'))
print('cas signalés :', tot, '; expliqués par la précision ou l ex æquo :', expl)

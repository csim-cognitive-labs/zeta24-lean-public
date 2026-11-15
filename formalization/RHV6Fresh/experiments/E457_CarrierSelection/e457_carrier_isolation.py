#!/usr/bin/env python3
"""E457 — volet déterministe (jumeau de Φ1, §19.82). Aucun paramètre libre, aucune graine : premiers ≤ 10⁶ par crible, 200 premières
hauteurs d'Odlyzko. Pour chaque Tour (β, T) : marge radiale maximale Δβ_max (formule tangentielle exacte) et marge en hauteur ΔT_max
(résolution monotone) conservant TOUT le mot sur les premiers ≤ 10⁶ ; vérification directe aux deux bords ; comparaison au demi-écart
entre hauteurs consécutives ; contrôles à β perturbé (0,3 ; 0,4 ; 0,45) aux mêmes hauteurs. Mesure, aucune loi."""
import sys, math
import numpy as np

ZFILE = sys.argv[1] if len(sys.argv) > 1 else '../data/odlyzko_zeros1_first5000.txt'
out = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s, flush=True); out.append(s)

N = 10**6
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0].astype(np.float64)
logp = np.log(primes)
heights = np.array([float(l.split()[0]) for l in open(ZFILE) if l.strip()])[:201]
T0 = heights[:200]
P('# E457 volet déterministe — premiers ≤', N, ':', len(primes), '; hauteurs :', len(T0), '(première', T0[0], ', dernière', T0[-1], ')')

def stage(beta, T):
    return (T * logp - math.atan(T / beta)) / math.pi

def dbeta_max(beta, T):
    s = stage(beta, T); f = s - np.floor(s)
    theta = math.atan(T / beta) - math.pi * (1.0 - f)           # arctan(T/β') doit rester > θ_q
    cand = np.full_like(s, 1.0 - beta)                          # plafond : β' < 1
    pos = theta > 0
    cand[pos] = np.minimum(T / np.tan(theta[pos]) - beta, 1.0 - beta)
    j = int(np.argmin(cand))
    return float(cand[j]), int(primes[j]), float(f[j]), np.floor(s)

def dT_max(beta, T):
    s = stage(beta, T); k1 = np.floor(s) + 1.0
    Tp = np.full_like(s, T)
    for _ in range(40):                                          # Newton sur g(T') = T' log q − arctan(T'/β) − π(⌊s⌋+1), g' > 0
        g = Tp * logp - np.arctan(Tp / beta) - math.pi * k1
        gp = logp - beta / (beta**2 + Tp**2)
        Tp = Tp - g / gp
    j = int(np.argmin(Tp - T))
    return float(Tp[j] - T), int(primes[j]), float((s - np.floor(s))[j])

def check(beta, T, floors, beta2, T2):
    return bool(np.all(np.floor(stage(beta2, T2)) == floors))

def run(beta_fn, label):
    P('\n##', label)
    rows = []
    viol = 0
    for k, T in enumerate(T0):
        beta = beta_fn(T)
        db, pb, fb, floors = dbeta_max(beta, T)
        dt, pt, ft = dT_max(beta, T)
        # vérification directe : juste en deçà de la marge, mot conservé ; juste au-delà, au moins une cellule change
        ok_in = check(beta, T, floors, beta + db * (1 - 1e-6), T) and check(beta, T, floors, beta, T + dt * (1 - 1e-6))
        ok_out = (not check(beta, T, floors, beta + db * (1 + 1e-3), T)) if beta + db * (1 + 1e-3) < 1 else True
        ok_out = ok_out and (not check(beta, T, floors, beta, T + dt * (1 + 1e-3)))
        if not (ok_in and ok_out): viol += 1
        halfgap_up = (heights[k + 1] - T) / 2
        rows.append((T, beta, db, pb, fb, dt, pt, ft, halfgap_up))
    r = np.array([(a[2], a[5], a[8], a[4], a[7]) for a in rows])
    P('vérification directe aux deux bords : violations', viol, '/', len(rows))
    P('Δβ_max  : min %.3e  médiane %.3e  max %.3e' % (r[:,0].min(), np.median(r[:,0]), r[:,0].max()))
    P('ΔT_max  : min %.3e  médiane %.3e  max %.3e' % (r[:,1].min(), np.median(r[:,1]), r[:,1].max()))
    P('demi-écart vers la hauteur suivante : min %.4f  médiane %.4f' % (r[:,2].min(), np.median(r[:,2])))
    P('rapport ΔT_max / demi-écart : max %.3e  médiane %.3e' % ((r[:,1]/r[:,2]).max(), np.median(r[:,1]/r[:,2])))
    P('fraction de cellule au premier limitant : Δβ médiane %.6f (attendu proche de 1) ; ΔT médiane %.6f' % (np.median(r[:,3]), np.median(r[:,4])))
    P('approximation ΔT ≈ π(1−f)/log q au premier limitant : erreur relative max %.2e' %
      max(abs(a[5] - math.pi * (1 - a[7]) / math.log(a[6])) / a[5] for a in rows))
    P('trois premières hauteurs : ' + ' ; '.join('T=%.4f β=%.2f Δβ=%.3e (p=%d) ΔT=%.3e (p=%d)' % (a[0], a[1], a[2], a[3], a[5], a[6]) for a in rows[:3]))
    return r

line = run(lambda T: 0.5, 'Ligne (β = 1/2), 200 hauteurs de zéros')
ctrl = {}
for b in (0.3, 0.4, 0.45):
    ctrl[b] = run(lambda T, b=b: b, 'Contrôle β = %.2f aux mêmes hauteurs (Tours non porteuses)' % b)
P('\n## Comparaison ligne / contrôles (la marge est-elle une propriété du mot, pas du poids ?)')
for b, r in ctrl.items():
    P('β = %.2f : médiane Δβ_max contrôle/ligne %.3f ; médiane ΔT_max contrôle/ligne %.3f ; corrélation des rangs ΔT (ligne vs contrôle) %.3f'
      % (b, np.median(r[:,0]) / np.median(line[:,0]), np.median(r[:,1]) / np.median(line[:,1]),
         np.corrcoef(np.argsort(np.argsort(line[:,1])), np.argsort(np.argsort(r[:,1])))[0,1]))
P('\n## Lecture (mesure, aucune loi)')
P('Pour chaque Tour, porteuse ou non, il existe une Tour voisine de même hauteur (β décalé) et une Tour voisine de même position radiale '
  '(T décalé) ayant exactement le même mot sur les 78 498 premiers ≤ 10⁶ ; la marge en hauteur est très inférieure au demi-écart entre zéros ; '
  'les marges des contrôles sont du même ordre que celles de la ligne.')
open('logs/e457_output.txt', 'w').write('\n'.join(out) + '\n')

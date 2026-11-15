#!/usr/bin/env python3
"""E458 — volet déterministe (jumeau de B0, B1, B4 ; §19.87). Aucun paramètre libre, aucune graine : premiers ≤ 10⁶ par crible, 200
premières hauteurs d'Odlyzko, ligne (β = 1/2) et Tours de contrôle β ∈ {0,3 ; 0,4 ; 0,45} aux mêmes hauteurs (non porteuses : aucun zéro
hors ligne n'est supposé ni testé). Mesures : effectif de la bande, premier premier de bande ; vérifications : B0 (écart des mots
exactement +1 sur la bande, 0 ailleurs) et B4 dans les deux sens (premier de bande ⟺ dans l'intervalle [contact du miroir, contact de
même indice de la Tour[). Cas dont la marge au bord est sous 1e-9 comptés à part (bruit de la double précision). Mesure, aucune loi,
aucune densité."""
import sys, math
import numpy as np

ZFILE = sys.argv[1]
out = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s, flush=True); out.append(s)

N = 10**6
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0].astype(np.float64)
logp = np.log(primes)
T0 = np.array([float(l.split()[0]) for l in open(ZFILE) if l.strip()])[:200]
P('# E458 volet déterministe — premiers ≤', N, ':', len(primes), '; hauteurs :', len(T0), '(première', T0[0], ', dernière', T0[-1], ')')
TOL = 1e-9

def stage(beta, T):
    return (T * logp - math.atan(T / beta)) / math.pi

def run(beta, label):
    P('\n##', label)
    counts = []; firsts = []
    b0_viol = 0; b4_fwd_viol = 0; b4_bwd_viol = 0; noisy = 0; empty = 0
    for T in T0:
        s = stage(beta, T); sm = stage(1.0 - beta, T)
        w = np.floor(s); wm = np.floor(sm)
        d = wm - w
        strip = d != 0
        # marge au bord : distance des deux positions d'étage à l'entier le plus proche
        marg = np.minimum(np.abs(s - np.round(s)), np.abs(sm - np.round(sm)))
        near = marg < TOL
        noisy += int(np.count_nonzero(near))
        ok = ~near
        # B0 : sur la bande l'écart vaut exactement +1 (côté bas) ; sur la ligne il vaut 0 partout
        b0_viol += int(np.count_nonzero(ok & strip & (d != 1)))
        # B4 sens direct : premier de bande ⟹ contact_miroir(k) ≤ p < contact_Tour(k) avec k = mot du miroir ;
        # en position d'étage : k ≤ sm et s < k
        k = wm
        inside_k = (k <= sm) & (s < k)
        b4_fwd_viol += int(np.count_nonzero(ok & strip & ~inside_k))
        # B4 sens réciproque : s'il existe un entier k avec s < k ≤ sm, le premier est de bande ; le seul candidat est ⌊s⌋+1
        exists_k = (w + 1.0) <= sm
        b4_bwd_viol += int(np.count_nonzero(ok & exists_k & ~strip))
        c = int(np.count_nonzero(strip)); counts.append(c)
        if c == 0: empty += 1; firsts.append(None)
        else: firsts.append(int(primes[int(np.argmax(strip))]))
    counts = np.array(counts)
    P('hauteurs à bande vide jusqu à 10^6 :', empty, '/', len(T0))
    P('effectif de bande : min', int(counts.min()), '; médiane', float(np.median(counts)), '; max', int(counts.max()), '; total', int(counts.sum()))
    P('effectifs aux hauteurs 1, 2, 3, 50, 100, 200 :', [int(counts[i]) for i in (0, 1, 2, 49, 99, 199)])
    P('premier premier de bande aux hauteurs 1, 2, 3, 50, 100, 200 :', [firsts[i] for i in (0, 1, 2, 49, 99, 199)])
    P('violations B0 :', b0_viol, '; B4 direct :', b4_fwd_viol, '; B4 réciproque :', b4_bwd_viol, '; cas sous le bruit (écartés) :', noisy)
    return empty, b0_viol + b4_fwd_viol + b4_bwd_viol, noisy

res = {}
res['ligne'] = run(0.5, 'ligne β = 1/2')
for b in (0.3, 0.4, 0.45):
    res[b] = run(b, 'contrôle β = %s' % b)
P('\n## Bilan')
P('ligne : bande vide aux 200 hauteurs :', res['ligne'][0] == 200)
P('violations B0/B4 toutes Tours :', sum(v[1] for v in res.values()), '; cas sous le bruit :', sum(v[2] for v in res.values()))
open(sys.argv[2], 'w').write('\n'.join(out) + '\n')

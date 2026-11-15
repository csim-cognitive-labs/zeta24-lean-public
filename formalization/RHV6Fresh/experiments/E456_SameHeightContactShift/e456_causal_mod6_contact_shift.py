#!/usr/bin/env python3
"""E456 — volet déterministe (§19.79.3). Aucun paramètre libre, aucune graine : tout est calculé depuis les premiers (crible)
et les 5 000 premières hauteurs d'Odlyzko. P1 jumeau de K6 ; P2 audit du texte collé (transitions mod 6) ; P3 question de la
gaussienne ; P4 causalité ON/OFF : intervention sur β à T fixée, contrôle : intervention sur T à β fixée."""
import sys, math, itertools, collections
import numpy as np
from scipy import stats

HERE = sys.argv[1] if len(sys.argv) > 1 else '.'
ZFILE = sys.argv[2] if len(sys.argv) > 2 else '../data/odlyzko_zeros1_first5000.txt'
out = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); out.append(s)

# ---------- premiers ----------
N = 10**6
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0]
pg = primes[primes > 3]                       # états ±1 mod 6
gaps = np.diff(pg)
cls = gaps % 6                                 # 0 maintien, 4 : 1→5 (τ15), 2 : 5→1 (τ51)
assert set(np.unique(cls)) <= {0, 2, 4}
state = pg % 6                                 # 1 ou 5
def tname(i):
    s, d = state[i], state[i+1]
    return {(1,1):'t11',(1,5):'t15',(5,1):'t51',(5,5):'t55'}[(s,d)]
# cohérence classe d'écart ↔ transition (compilé : eventOrientation_of_gap)
for i in range(0, 20000):
    t = tname(i); c = cls[i]
    assert (t in ('t11','t55')) == (c == 0) and (t == 't15') == (c == 4) and (t == 't51') == (c == 2)
P('# E456 volet déterministe — premiers ≤', N, ': nombre', len(primes), '; premiers > 3 :', len(pg), '; transitions :', len(gaps))

# ---------- P2 : audit du texte collé ----------
P('\n## P2 — recompte des quatre transitions')
def counts(n0, n1):
    c = collections.Counter(tname(i) for i in range(n0, n1))
    return {k: c.get(k, 0) for k in ('t11','t15','t51','t55')}
for label, n in (('5 000 premiers écarts (p>3)', 5000), ('799 fenêtres × 12 = 9 588 transitions', 9588)):
    c = counts(0, n)
    P(f'{label} : {c} ; somme {sum(c.values())} ; τ15−τ51 = {c["t15"]-c["t51"]} ; premier état {state[0]}, dernier état {state[n]} ;'
      f' τ11−τ55 = {c["t11"]-c["t55"]} ; croisements {c["t15"]+c["t51"]} ({(c["t15"]+c["t51"])/n:.4f}), maintiens {c["t11"]+c["t55"]}')
P('texte collé : t11 994, t15 1490, t51 1490, t55 1026 (somme 5000) ; « 9 590 premiers », « 799 fenêtres » (9 588 transitions) : incohérent')
# télescopage : bilan orienté sur tout préfixe ∈ {-1,0,1}, nul ⟺ même état aux deux bouts
orient = np.where(cls == 4, 1, np.where(cls == 2, -1, 0))
bal = np.cumsum(orient)
P('bilan orienté : min', int(bal.min()), 'max', int(bal.max()), '; nul ⟺ même état aux bouts :',
  bool(np.all((bal == 0) == (state[1:] == state[0]))))
P('premiers > 3 jusqu\'au rang : 9 590 premiers ≠ 5 001 premiers pour 5 000 écarts ; 799×12+1 = 9 589 premiers')

# énumération exacte des 2^13 = 8192 mots valides
P('\n## P2 — énumération exacte des 8 192 mots de douze transitions (13 états)')
dist_cross = collections.Counter(); dist_d = collections.Counter(); cl = collections.Counter(); cand = collections.Counter()
for bits in itertools.product((1, 5), repeat=13):
    n11 = sum(1 for a, b in zip(bits, bits[1:]) if a == 1 and b == 1)
    n55 = sum(1 for a, b in zip(bits, bits[1:]) if a == 5 and b == 5)
    cr = 12 - n11 - n55
    dist_cross[cr] += 1; dist_d[n11 - n55] += 1
    cl['B egalite' if n11 == n55 else ('C famille1' if n11 > n55 else 'D famille5')] += 1
    cand['croisements >= 7'] += cr >= 7; cand['croisements >= 6'] += cr >= 6; cand['croisements > maintiens'] += cr > 12 - cr
    cand['croisements >= 8'] += cr >= 8; cand['n11=n55 ou cr>=7'] += (n11 == n55) or cr >= 7
P('total', sum(cl.values()), '; classes :', {k: f'{v} ({v/8192:.4f})' for k, v in sorted(cl.items())}, '; somme des parts', round(sum(cl.values())/8192, 6))
P('texte : B 10,5 % C 43,8 % D 43,8 % (somme 98,1 %) — exact :', {k: round(v/8192*100, 2) for k, v in sorted(cl.items())})
P('candidats pour « A » (texte 51,9 %) :', {k: round(v/8192*100, 2) for k, v in cand.items()})
P('nombre de croisements sous l\'uniforme :', dict(sorted(dist_cross.items())), '= binomiale(12,1/2) :',
  all(dist_cross[c] == math.comb(12, c) for c in range(13)))
# fenêtres réelles de 12
W = 12; nwin = len(gaps) // W
wc = cls[:nwin*W].reshape(nwin, W)
st = state[:nwin*W+1]
n11w = np.array([sum(1 for j in range(W) if st[i*W+j] == 1 and st[i*W+j+1] == 1) for i in range(nwin)])
n55w = np.array([sum(1 for j in range(W) if st[i*W+j] == 5 and st[i*W+j+1] == 5) for i in range(nwin)])
crw = W - n11w - n55w
for lab, sl in (('799 premières fenêtres', slice(0, 799)), (f'toutes ({nwin}) fenêtres ≤ 10^6', slice(0, nwin))):
    a, b = n11w[sl], n55w[sl]; n = len(a)
    P(f'{lab} : B {np.sum(a==b)/n:.4f} C {np.sum(a>b)/n:.4f} D {np.sum(a<b)/n:.4f} (somme 1) ; croisements≥7 {np.sum(crw[sl]>=7)/n:.4f} ;'
      f' croisements moyens {crw[sl].mean():.4f} (uniforme : 6) ; texte : 56,5 / 10,6 / 40,4 / 42,4 (somme 93,4)')

# ---------- P3 : Gauss ? ----------
P('\n## P3 — la distribution du nombre de croisements est-elle gaussienne ?')
def describe(x, n):
    x = np.asarray(x, float); m, s = x.mean(), x.std(ddof=1)
    sk, ku = stats.skew(x), stats.kurtosis(x)           # kurtosis excédentaire (0 pour la normale)
    phat = m / n
    disp = x.var(ddof=1) / (n * phat * (1 - phat))
    ks = stats.kstest((x - m) / s, 'norm').statistic
    return m, s, sk, ku, phat, disp, ks
m, s, sk, ku, phat, disp, ks = describe(crw, 12)
P(f'fenêtres de 12 ({nwin}) : moyenne {m:.4f} écart-type {s:.4f} p̂ {phat:.4f} ; asymétrie {sk:.4f} aplatissement exc. {ku:.4f} ;'
  f' dispersion var/(np(1−p)) {disp:.4f} ; support 13 valeurs (discret) ; KS contre normale ajustée {ks:.4f}')
obs = np.bincount(crw, minlength=13)
for lab, p in (('binomiale(12, 1/2)', 0.5), ('binomiale(12, p̂)', phat)):
    exp = nwin * np.array([math.comb(12, c) * p**c * (1-p)**(12-c) for c in range(13)])
    mask = exp >= 5
    chi = np.sum((obs[mask] - exp[mask])**2 / exp[mask])
    P(f'  khi-deux contre {lab} : {chi:.1f} sur {mask.sum()-1} ddl (p≈{1-stats.chi2.cdf(chi, mask.sum()-1 - (lab.endswith("p̂)"))):.2e})')
P('  histogramme réel (0..12) :', obs.tolist(), '; binomiale(12,p̂) :', [int(round(nwin*math.comb(12,c)*phat**c*(1-phat)**(12-c))) for c in range(13)])
for Wn in (120, 1200, 12000):
    nw = len(gaps) // Wn
    crs = (cls[:nw*Wn].reshape(nw, Wn) != 0).sum(axis=1)
    m, s, sk, ku, phat, disp, ks = describe(crs, Wn)
    sw = stats.shapiro(crs).pvalue if nw <= 5000 else float('nan')
    P(f'fenêtres de {Wn} ({nw}) : p̂ {phat:.4f} asymétrie {sk:.4f} aplatissement exc. {ku:.4f} dispersion {disp:.4f} KS {ks:.4f} Shapiro p {sw:.3g}')
# biais des résidus consécutifs : maintien attendu 1/2 sous l'indépendance
P('biais : part des maintiens sur tous les écarts ≤ 10^6 :', round(float(np.mean(cls == 0)), 4), '(indépendance : 0,5) ; t11', int(np.sum((state[:-1]==1)&(state[1:]==1))), 't55', int(np.sum((state[:-1]==5)&(state[1:]==5))))

# ---------- hauteurs ----------
heights = []
for line in open(ZFILE):
    tok = line.split()
    if not tok: continue
    try: heights.append(float(tok[0]))
    except ValueError: pass
heights = np.array(heights); assert len(heights) >= 5000, len(heights)
heights = heights[:5000]
P('\n## P1 — jumeau de K6 sur', len(heights), 'hauteurs réelles (première', heights[0], ', dernière', heights[-1], ')')
def phase(b, T): return math.atan(T / b)
def contact(b, T, k): return math.exp((phase(b, T) + k * math.pi) / T)
worst_ratio = 0.0; worst_shift = 0.0; min_grid = float('inf'); viol = 0
for T in heights:
    for b in (0.3, 0.4):
        # M5 : rapport de cellule indépendant de β (k = 7, 8)
        r_off = math.log(contact(b, T, 8)) - math.log(contact(b, T, 7)); r_on = math.log(contact(0.5, T, 8)) - math.log(contact(0.5, T, 7))
        worst_ratio = max(worst_ratio, abs(r_off - r_on), abs(r_on - math.pi / T))
        # M4 : décalage dans ]−π/(2T), π/(2T)[ en logarithme
        d = (phase(b, T) - phase(0.5, T)) / T
        worst_shift = max(worst_shift, abs(d) / (math.pi / (2 * T)))
        if not (-math.pi/(2*T) < d < math.pi/(2*T)): viol += 1
        # M1 : distance minimale entre les deux grilles (en logarithme, modulo le pas)
        g = abs(d) % (math.pi / T); g = min(g, math.pi / T - g)
        min_grid = min(min_grid, g * T / math.pi)     # en fraction de cellule
P(f'M5 : écart maximal entre rapports de cellule ON/OFF et avec π/T : {worst_ratio:.2e}')
P(f'M4 : décalage / demi-cellule, maximum {worst_shift:.4f} (< 1 attendu) ; violations {viol}')
P(f'M1 : distance minimale entre grilles ON et OFF, en fraction de cellule : {min_grid:.3e} (> 0 attendu) ; décroît en (1−2β)/(πT)×... : '
  f'β=0,3 à T={heights[-1]:.2f} : {(phase(0.3,heights[-1])-phase(0.5,heights[-1]))/math.pi:.3e}')

# ---------- P4 : causalité ON/OFF ----------
P('\n## P4 — intervention sur β à T fixée (grille des rencontres), contrôle : intervention sur T à β fixée')
logp = np.log(pg.astype(float))
def touched(b, T):
    sp = np.floor((T * logp - phase(b, T)) / math.pi)      # lastContactBefore = ⌊stagePosition⌋
    return sp[:-1] < sp[1:]                                  # GapHasContact
def frac(b, T):
    sp = (T * logp - phase(b, T)) / math.pi
    return sp - np.floor(sp)                                 # cellFraction au premier
sel = heights[::25]                                           # 200 hauteurs, déterministe
jac_b, jac_T, comp = [], [], {0.5: np.zeros(3), 0.3: np.zeros(3)}
chi_on, chi_off = [], []
share_on, share_off = [], []
for idx, T in enumerate(sel):
    on, off = touched(0.5, T), touched(0.3, T)
    inter, uni = np.sum(on & off), np.sum(on | off)
    jac_b.append(inter / uni)
    share_on.append(on.mean()); share_off.append(off.mean())
    for b, tm in ((0.5, on), (0.3, off)):
        c = cls[tm]
        comp[b] += np.array([np.mean(c == 0), np.mean(c == 4), np.mean(c == 2)]) / len(sel)
        # contingence type de transition × quartile de la fraction de cellule au premier de départ (tous les écarts)
        f = frac(b, T)[:-1]
        q = np.minimum((f * 4).astype(int), 3)
        tab = np.zeros((3, 4))
        for ci, cv in enumerate((0, 4, 2)):
            for qi in range(4): tab[ci, qi] = np.sum((cls == cv) & (q == qi))
        chi2, pval = stats.chi2_contingency(tab)[:2]
        (chi_on if b == 0.5 else chi_off).append(pval)
    # contrôle : T → hauteur suivante, β fixée
    i = idx * 25
    if i + 1 < len(heights):
        on2 = touched(0.5, heights[i + 1])
        jac_T.append(np.sum(on & on2) / np.sum(on | on2))
jac_b, jac_T = np.array(jac_b), np.array(jac_T)
P(f'écarts touchés (≤ 10^6, {len(gaps)} écarts) : part ON {np.mean(share_on):.4f}, part OFF {np.mean(share_off):.4f}')
P(f'recouvrement de Jaccard des écarts touchés, β 0,5 → 0,3 à T fixée : moyenne {jac_b.mean():.4f}, min {jac_b.min():.4f}, max {jac_b.max():.4f}')
P(f'contrôle, T → hauteur suivante à β fixée : moyenne {jac_T.mean():.4f}, min {jac_T.min():.4f}, max {jac_T.max():.4f}')
P('composition mod 6 des écarts touchés (maintien, τ15, τ51) : ON', np.round(comp[0.5], 4).tolist(), '; OFF', np.round(comp[0.3], 4).tolist(),
  '; tous les écarts', np.round([np.mean(cls==0), np.mean(cls==4), np.mean(cls==2)], 4).tolist())
P(f'contingence type × quartile de fraction de cellule : p-valeurs ON médiane {np.median(chi_on):.3f} (part < 0,05 : {np.mean(np.array(chi_on)<0.05):.3f}) ;'
  f' OFF médiane {np.median(chi_off):.3f} (part < 0,05 : {np.mean(np.array(chi_off)<0.05):.3f}) ; attendu sous indépendance : 0,05')
# intervention sur T à β fixée : pas, phase, contacts (height_advance_concurs)
T1, T2 = heights[0], heights[1]
P(f'intervention sur T (β = 1/2) : pas π/T {math.pi/T1:.5f} → {math.pi/T2:.5f} ; phase {phase(0.5,T1):.6f} → {phase(0.5,T2):.6f} ;'
  f' contact k=1 {contact(0.5,T1,1):.4f} → {contact(0.5,T2,1):.4f}')
P(f'intervention sur β (T = {T1:.4f}) : pas {math.pi/T1:.5f} → {math.pi/T1:.5f} (identique) ; phase {phase(0.5,T1):.6f} → {phase(0.3,T1):.6f} ;'
  f' contact k=1 {contact(0.5,T1,1):.4f} → {contact(0.3,T1,1):.4f} ; facteur {contact(0.3,T1,1)/contact(0.5,T1,1):.6f} ∈ ]{math.exp(-math.pi/(2*T1)):.6f}, {math.exp(math.pi/(2*T1)):.6f}[')
open(f'{HERE}/logs/e456_output.txt', 'w').write('\n'.join(out) + '\n')

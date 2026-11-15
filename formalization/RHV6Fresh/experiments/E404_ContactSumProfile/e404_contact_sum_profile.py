# E404 — Somme des contacts sur l'axe réel le long de chaque écart : montée, cassure, redescente (pré-enregistré dans README.md).
# Usage : python3 -I e404_contact_sum_profile.py <zeros_file> <prime_bound> <outdir>
# Borné (< 15 min). Aucune sortie fabriquée. Deux canaux SÉPARÉS : brut (non compilé) et lissé (compilé, E402/E403).
import sys, os, hashlib, time, math
import numpy as np
from mpmath import mp, mpf, mpc, zeta, log as mlog, quad, inf, nsum, exp as mexp, pi as mpi

t0 = time.time()
zfile, PB, outdir = sys.argv[1], int(sys.argv[2]), sys.argv[3]
os.makedirs(outdir, exist_ok=True)
mp.dps = 30
LOG = open(os.path.join(outdir, 'e404_run_log.txt'), 'w')
def log(s):
    LOG.write("[%7.1f s] %s\n" % (time.time() - t0, s)); LOG.flush(); print(s, flush=True)

# ---------- 0. Provenance ----------
h = hashlib.sha256(open(zfile, 'rb').read()).hexdigest()
ref = open(zfile + '.sha256').read().split()[0]
assert h == ref, ('SHA-256 mismatch', h, ref)
T = np.loadtxt(zfile, dtype=np.float64)
NZ = len(T); assert NZ == 2001052 and np.all(np.diff(T) > 0)
Tmax = float(T[-1])
prov = ["zeros: %s" % zfile, "sha256: %s (== .sha256)" % h, "N = %d ; T_1 = %.9f ; T_max = %.9f" % (NZ, T[0], Tmax),
        "hypothèse de données : hauteurs de zéros connus posés sur la ligne (β = 1/2) ; ne certifient pas l'absence de zéros OFF"]
log("zéros chargés")

# ---------- 1. Vrais écarts : premiers, Λ, ψ et A exacts ----------
def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
Pall = sieve(2 * PB)
P = [p for p in Pall if p <= PB]; P.append(Pall[len(P)])
NP = len(P); NG = NP - 1
Lam = np.zeros(P[-1] + 3)
for p in Pall:
    q = p
    while q <= P[-1] + 2: Lam[q] = math.log(p); q *= p
m = np.arange(len(Lam)); S0 = np.cumsum(Lam); S1 = np.cumsum(Lam * m)
def psi(x):   # x non entier : ψ(x) = Σ_{m ≤ x} Λ(m)
    return S0[int(math.floor(x))]
def A(x):     # A(x) = Σ_{m<x} Λ(m)(1 − m/x) ; pour x entier m<x strict
    k = int(math.ceil(x)) - 1; return S0[k] - S1[k] / x
def A_mp(x): return sum(mpf(Lam[k]) * (1 - mpf(int(k)) / mpf(x)) for k in range(2, int(math.ceil(x))) if Lam[k] != 0)
Pf = np.array(P, dtype=np.float64); logP = np.log(Pf); ell = np.diff(logP); gapA = np.diff(Pf)

# ---------- 2. Fonds ----------
lz0 = -(zeta(0, derivative=1) / zeta(0)); lzm1 = zeta(-1, derivative=1) / zeta(-1)
def triv(x):
    x = mpf(x); return nsum(lambda j: -(x ** (-2*(j+1))) / ((-2*(j+1)) * (-2*(j+1) + 1)), [0, inf])
def B(x): return float(mpf(x) / 2 + lz0 + lzm1 / x + triv(x))                # fond lissé (E401)
def Braw(x): return x - math.log(2 * math.pi) - 0.5 * math.log(1 - x ** (-2.0))   # fond brut
def true_raw(x): return Braw(x) - psi(x)        # = Σ_ρ x^ρ/ρ (vérité, par crible)
def true_sm(x):  return A(x) - B(x)             # = 2Re Σ_{γ>0} d_ρ(x) (vérité, par crible)
Zn = np.array([(A(P[n+1]) - A(P[n])) - (B(P[n+1]) - B(P[n])) for n in range(NG)])   # demande exacte de l'écart (lissé)
log("premiers, ψ, A, fonds prêts : %d écarts" % NG)

# ---------- 3. Poids des zéros ----------
rho = 0.5 + 1j * T
Wraw = 1.0 / rho                     # Σ x^ρ/ρ
Wsm = -1.0 / (rho * (rho + 1.0))     # d_ρ(x) = −x^ρ/(ρ(ρ+1))
CUT = [30.0, 100.0, 300.0, 1e3, 3e3, 1e4, 3e4, 1e5, 3e5]
def partials(x, bounds):
    """Somme signée 2Re Σ_{γ>0} pour les deux canaux, cumulée par blocs de rang [bounds] (indices croissants, bounds[-1]=NZ).
    Renvoie (raw_partials, sm_partials) : valeurs cumulées à chaque borne."""
    E = np.exp(1j * (T * math.log(x))) * math.sqrt(x)
    Vr = np.add.reduceat((E * Wraw).real, np.r_[0, bounds[:-1]])
    Vs = np.add.reduceat((E * Wsm).real, np.r_[0, bounds[:-1]])
    return 2 * np.cumsum(Vr), 2 * np.cumsum(Vs)

# ---------- 4. Écarts choisis ----------
n_maxgap = int(np.argmax(gapA)); n_twin = int(np.max(np.where(gapA == 2)[0]))
chosen = sorted(set([4, 614, 1228, n_maxgap, n_twin, 100, 300, 500, 800, 1000]))
NPTS = 100
def grid(n):
    xs = list(np.linspace(P[n] + 0.5, P[n+1] - 0.5, NPTS)); xs.append(P[n+1] + 0.5); return xs
def bounds_for(n):
    cuts = sorted(CUT + [math.pi / ell[n]])
    idx = [int(np.searchsorted(T, c, side='right')) for c in cuts] + [NZ]
    return cuts, idx
prof = {}   # n -> list of (x, true_raw, raw_partials, true_sm, sm_partials)
for n in chosen:
    cuts, idx = bounds_for(n)
    rows = []
    for x in grid(n):
        pr, ps = partials(x, idx)
        rows.append((x, true_raw(x), pr, true_sm(x), ps))
    prof[n] = (cuts, rows)
    log("profil écart n=%d [%d, %d] calculé" % (n, P[n], P[n+1]))

# ---------- 5. Fenêtre continue de six écarts (sans remise à zéro) ----------
WIN = list(range(614, 620))
cutsW = [1e3, 1e4, 1e5]; idxW = [int(np.searchsorted(T, c, side='right')) for c in cutsW] + [NZ]
win = []
for n in WIN:
    for x in np.linspace(P[n] + 0.5, P[n+1] - 0.5, NPTS):
        pr, ps = partials(x, idxW); win.append((n, x, true_raw(x), pr, true_sm(x), ps))
log("fenêtre continue n=614..619 calculée")

# ---------- 6. Jumeau OFF dégénéré, SÉPARÉ : bloc de zéros ON remplacé par des paires 0,3/0,7 ----------
j0 = 1999
blocks = [1, 50, 500]
Tstar_all = 0.5 * (T[j0:j0+500] + T[j0+1:j0+501])
dmin = min(np.min(np.abs(T[:, None] - Tstar_all[None, :k])) for k in [1]) if False else None
# distance de chaque hauteur synthétique au zéro le plus proche (les médianes sont strictement entre deux zéros)
dists = np.minimum(Tstar_all - T[j0:j0+500], T[j0+1:j0+501] - Tstar_all); assert dists.min() > 0
def twin_delta(x, mblk):
    """(Δraw, Δsm) = contribution des paires − contribution des ON retirés, pour un bloc de taille mblk."""
    r_on = rho[j0:j0+mblk]; ts = Tstar_all[:mblk]
    e_on = np.exp(r_on * math.log(x))
    out = []
    for W_of in (lambda r: 1.0 / r, lambda r: -1.0 / (r * (r + 1.0))):
        s = -np.sum(e_on * W_of(r_on))
        for b in (0.3, 0.7):
            r = b + 1j * ts; s += np.sum(np.exp(r * math.log(x)) * W_of(r))
        out.append(2 * s.real)
    return out
syn = {}
for n in chosen:
    rows = []
    for x in grid(n):
        rows.append((x, [twin_delta(x, mb) for mb in blocks]))
    syn[n] = rows
log("jumeau OFF (blocs 1, 50, 500) calculé")

# ---------- 7. Jumeaux mpmath (3 écarts, point p_{n+1} − 1/2, 2000 premiers zéros) ----------
tw = []
for n in [4, 614, 1228]:
    x = P[n+1] - 0.5; sr = mpf(0); ss = mpf(0)
    for j in range(2000):
        r = mpc(mpf('0.5'), mpf(float(T[j]))); e = mexp(r * mlog(x))
        sr += 2 * (e / r).real; ss += 2 * (-e / (r * (r + 1))).real
    E = np.exp(1j * (T[:2000] * math.log(x))) * math.sqrt(x)
    nr = 2 * np.sum((E * Wraw[:2000]).real); ns = 2 * np.sum((E * Wsm[:2000]).real)
    tw.append("n=%d x=%.1f (2000 zéros) : brut mpmath − numpy = %.2e ; lissé mpmath − numpy = %.2e ; A mpmath − flottant = %.2e ; ψ exact = %.9f"
              % (n, x, abs(float(sr) - nr), abs(float(ss) - ns), abs(float(A_mp(x)) - A(x)), psi(x)))
log("jumeaux mpmath faits")

# ---------- 8. Sorties ----------
def fmt(v): return " ".join("%.6e" % t for t in v)
with open(os.path.join(outdir, 'e404_profiles.txt'), 'w') as f:
    f.write("# Profils par écart choisi. Cumul depuis le premier point de la grille (x0 = p_n + 1/2). Colonnes :\n")
    f.write("# n x | BRUT : vérité C_true(x) ; C_tronq(x) aux seuils (liste par écart, dernier = tous) ; résidu (tous − vérité) | LISSÉ : vérité ; tronq aux mêmes seuils ; résidu\n")
    for n in chosen:
        cuts, rows = prof[n]
        f.write("# écart n=%d : p_n=%d p_{n+1}=%d écart arithmétique=%d log p_{n+1}=%.9f demande lissée Z_n=%.9e ; seuils de fréquence : %s ; seuil de foule π/ℓ=%.3f\n"
                % (n, P[n], P[n+1], P[n+1]-P[n], logP[n+1], Zn[n], " ".join("%.0f" % c for c in cuts) + " Tmax", math.pi / ell[n]))
        x0, tr0, pr0, ts0, ps0 = rows[0]
        for (x, tr, pr, ts, ps) in rows:
            f.write("%d %.6f | %.9e %s %.3e | %.9e %s %.3e\n" % (n, x, tr - tr0, fmt(pr - pr0), (pr[-1]-pr0[-1]) - (tr - tr0), ts - ts0, fmt(ps - ps0), (ps[-1]-ps0[-1]) - (ts - ts0)))
with open(os.path.join(outdir, 'e404_window.txt'), 'w') as f:
    f.write("# Fenêtre continue n=614..619, SANS remise à zéro : cumul depuis x0 = p_614 + 1/2. Seuils 1000 10000 100000 Tmax.\n")
    f.write("# n x | BRUT vérité ; tronq(4) ; résidu | LISSÉ vérité ; tronq(4) ; résidu\n")
    n0, x0, tr0, pr0, ts0, ps0 = win[0]
    for (n, x, tr, pr, ts, ps) in win:
        f.write("%d %.6f | %.9e %s %.3e | %.9e %s %.3e\n" % (n, x, tr - tr0, fmt(pr - pr0), (pr[-1]-pr0[-1]) - (tr - tr0), ts - ts0, fmt(ps - ps0), (ps[-1]-ps0[-1]) - (ts - ts0)))
with open(os.path.join(outdir, 'e404_freq_decomposition.txt'), 'w') as f:
    f.write("# Décomposition par fréquence croissante, par écart choisi : MONTÉE = S(p_{n+1}−1/2) − S(p_n+1/2) ; CHUTE = S(p_{n+1}+1/2) − S(p_{n+1}−1/2).\n")
    f.write("# Chaque ligne : seuil T ; nb de zéros ≤ T ; montée brute cumulée ; chute brute cumulée ; montée lissée cumulée ; chute lissée cumulée. Vérités en tête.\n")
    for n in chosen:
        cuts, rows = prof[n]; xa, tra, pra, tsa, psa = rows[0]; xb, trb, prb, tsb, psb = rows[-2]; xc, trc, prc, tsc, psc = rows[-1]
        f.write("# écart n=%d [%d, %d] : VÉRITÉ montée brute = %.9f (écart arithmétique − 1 = %d, moins sauts de puissances de premiers intérieurs) ; VÉRITÉ chute brute = %.9f (= 1 − log p_{n+1} = %.9f) ; VÉRITÉ montée lissée = %.9e ; VÉRITÉ chute lissée = %.9e ; seuil de foule π/ℓ = %.3f\n"
                % (n, P[n], P[n+1], trb - tra, P[n+1]-P[n]-1, trc - trb, 1 - logP[n+1], tsb - tsa, tsc - tsb, math.pi / ell[n]))
        idx = [int(np.searchsorted(T, c, side='right')) for c in cuts] + [NZ]
        for i, c in enumerate(cuts + [Tmax]):
            f.write("%d %.3f %d %.9f %.9f %.9e %.9e\n" % (n, c, idx[i], prb[i]-pra[i], prc[i]-prb[i], psb[i]-psa[i], psc[i]-psb[i]))
with open(os.path.join(outdir, 'e404_synthetic.txt'), 'w') as f:
    f.write("# SYNTHÉTIQUE, SÉPARÉ : bloc de zéros ON (rangs 2000.., tailles %s) REMPLACÉ par des paires 0,3/0,7 aux hauteurs médianes (distance min au zéro le plus proche %.4e, toutes > 0)\n" % (blocks, dists.min()))
    f.write("# n x | Δbrut(bloc 1) Δbrut(50) Δbrut(500) | résidu brut réel (tous − vérité) | Δlissé(1) Δlissé(50) Δlissé(500) | résidu lissé réel\n")
    f.write("# Δ = (somme avec paires) − (somme réelle), au même point x ; le profil jumeau est le profil réel + Δ.\n")
    for n in chosen:
        cuts, rows = prof[n]
        for (x, tr, pr, ts, ps), (x2, dl) in zip(rows, syn[n]):
            assert x == x2
            f.write("%d %.6f | %s | %.3e | %s | %.3e\n" % (n, x, " ".join("%.6e" % d[0] for d in dl), pr[-1] - tr, " ".join("%.6e" % d[1] for d in dl), ps[-1] - ts))
with open(os.path.join(outdir, 'e404_summary.txt'), 'w') as f:
    f.write("E404 — exécution du %s ; durée %.1f s ; premiers ≤ %d (%d écarts) ; écarts choisis %s ; fenêtre continue %d..%d\n" % (time.strftime('%Y-%m-%d %H:%M:%S'), time.time() - t0, PB, NG, chosen, WIN[0], WIN[-1]))
    for s in prov: f.write("provenance : " + s + "\n")
    f.write("écart le plus long : n=%d [%d, %d] ; dernier écart de longueur 2 : n=%d [%d, %d]\n" % (n_maxgap, P[n_maxgap], P[n_maxgap+1], n_twin, P[n_twin], P[n_twin+1]))
    f.write("1. Par écart (toute la liste de zéros) : montée brute calculée / vérité ; chute brute calculée / vérité ; pente brute min/max sur la grille (vérité = 1 hors puissances de premiers) ; résidu brut max sur la grille ; montée lissée calculée / Z_n ; résidu lissé max\n")
    for n in chosen:
        cuts, rows = prof[n]; xa, tra, pra, tsa, psa = rows[0]; xb, trb, prb, tsb, psb = rows[-2]; xc, trc, prc, tsc, psc = rows[-1]
        xs = np.array([r[0] for r in rows[:-1]]); vr = np.array([r[2][-1] for r in rows[:-1]]); slopes = np.diff(vr) / np.diff(xs)
        resr = max(abs(r[2][-1] - r[1]) for r in rows); ress = max(abs(r[4][-1] - r[3]) for r in rows)
        f.write("   n=%d [%d,%d] : montée brute %.6f / %.6f ; chute brute %.6f / %.6f (log p = %.6f) ; pente brute min %.4f max %.4f ; résidu brut max %.2e ; montée lissée %.9e / Z_n %.9e ; résidu lissé max %.2e\n"
                % (n, P[n], P[n+1], prb[-1]-pra[-1], trb-tra, prc[-1]-prb[-1], trc-trb, logP[n+1], slopes.min(), slopes.max(), resr, psb[-1]-psa[-1], tsb - tsa, ress))
    f.write("2. Décomposition par fréquence : voir e404_freq_decomposition.txt (montée et chute cumulées par seuil, les deux canaux).\n")
    f.write("3. Jumeau OFF : |Δ| au point p_{n+1}−1/2 par bloc, contre le résidu réel au même point\n")
    for n in chosen:
        cuts, rows = prof[n]; (x, tr, pr, ts, ps) = rows[-2]; (x2, dl) = syn[n][-2]
        f.write("   n=%d x=%.1f : brut |Δ| bloc1 %.3e bloc50 %.3e bloc500 %.3e (résidu brut %.3e) ; lissé |Δ| bloc1 %.3e bloc50 %.3e bloc500 %.3e (résidu lissé %.3e)\n"
                % (n, x, abs(dl[0][0]), abs(dl[1][0]), abs(dl[2][0]), abs(pr[-1]-tr), abs(dl[0][1]), abs(dl[1][1]), abs(dl[2][1]), abs(ps[-1]-ts)))
    f.write("4. Jumeaux mpmath (dps 30) :\n")
    for s in tw: f.write("   " + s + "\n")
    f.write("Aucune conclusion sur β des vrais zéros.\n")
log("E404 terminé")

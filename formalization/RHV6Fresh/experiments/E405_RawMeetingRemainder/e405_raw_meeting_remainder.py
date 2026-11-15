# E405 — reste brut aux points de rencontre (pré-enregistré dans README.md). Borné, réel, aucune sortie fabriquée.
# Usage : python3 -I e405_raw_meeting_remainder.py <zeros_file> <outdir>
import sys, os, hashlib, time, math
import numpy as np
from mpmath import mp, mpf, zeta, nsum, inf

t0 = time.time()
zfile, outdir = sys.argv[1], sys.argv[2]
os.makedirs(outdir, exist_ok=True)
out = open(os.path.join(outdir, 'e405_results.txt'), 'w')
def log(s):
    out.write(s + "\n"); out.flush(); print("[%6.1f s] %s" % (time.time() - t0, s), flush=True)

X = 2_000_000
# ---------- crible de Λ ----------
s = np.ones(X + 1, dtype=bool); s[:2] = False
for i in range(2, int(X ** 0.5) + 1):
    if s[i]: s[i*i::i] = False
primes = np.nonzero(s)[0]
Lam = np.zeros(X + 1)
for p in primes:
    q = p
    while q <= X:
        Lam[q] = math.log(p); q *= p
psi = np.cumsum(Lam)                       # ψ(N) = Σ_{m≤N} Λ(m)
N = np.arange(X + 1, dtype=np.float64)
r = psi - N                                # reste brut r(N) = ψ(N) − N
ev = Lam != 0                              # rencontres brutes (premiers et puissances)
E = np.nonzero(ev)[0]
log("Volet 1 — crible jusqu'à X = %d : %d premiers, %d rencontres brutes" % (X, len(primes), len(E)))

# identité 1 : descente d'une unité entre rencontres (tous N ≥ 1 non rencontre)
nonev = np.nonzero(~ev)[0]; nonev = nonev[nonev >= 1]
d = r[nonev] - r[nonev - 1]
log("identité 1 : max |r(N) − r(N−1) + 1| sur les %d entiers non-rencontre = %.3e" % (len(nonev), np.max(np.abs(d + 1))))
# identité 2 : M·A(M) = Σ_{k<M} ψ(k), A(M) = Σ_{n<M} Λ(n)(1 − n/M)
m = np.arange(X + 1); S1 = np.cumsum(Lam * m); cpsi = np.cumsum(psi)
for M in [10, 100, 1000, 4547, 100003, 1000003, X]:
    A = psi[M - 1] - S1[M - 1] / M
    lhs = M * A; rhs = cpsi[M - 1]
    log("identité 2 : M = %7d  M·A(M) = %.6f  Σ_{k<M} ψ(k) = %.6f  écart relatif = %.1e" % (M, lhs, rhs, abs(lhs - rhs) / max(1.0, abs(rhs))))
# bornes aux rencontres contre tout entier
Nf = N[1:]; rf = r[1:]
for th in [0.50, 0.52, 0.55, 0.60]:
    mE = np.max(np.abs(r[E]) / E ** th); mEm = np.max(np.abs(r[E - 1]) / E ** th)
    mN = np.max(np.abs(rf) / Nf ** th)
    argN = int(Nf[np.argmax(np.abs(rf) / Nf ** th)])
    bound = 2 ** th * max(mE, mEm) + 1
    log("θ = %.2f : max_E |r(E)|/E^θ = %.4f ; max_E |r(E−1)|/E^θ = %.4f ; max_N |r(N)|/N^θ = %.4f (en N = %d) ; "
        "borne compilée 2^θ·max_E + 1 = %.4f ; respectée : %s" % (th, mE, mEm, mN, argN, bound, mN <= bound + 1e-12))
# tranches dyadiques
log("tranches dyadiques [2^j, 2^{j+1}) : max_E |r(E)|/√E, et le E qui le réalise")
for j in range(4, 21):
    lo, hi = 2 ** j, min(2 ** (j + 1), X + 1)
    sel = E[(E >= lo) & (E < hi)]
    if len(sel) == 0: continue
    v = np.abs(r[sel]) / np.sqrt(sel); k = int(np.argmax(v))
    log("  j = %2d : %.4f en E = %d (r = %+.3f)" % (j, v[k], sel[k], r[sel[k]]))

# ---------- Volet 2 — tentative A : reste lissé aux rencontres ----------
mp.dps = 25
lz0 = -(zeta(0, derivative=1) / zeta(0)); lzm1 = zeta(-1, derivative=1) / zeta(-1)
def triv(x):
    x = mpf(x); return nsum(lambda j: -(x ** (-2*(j+1))) / ((-2*(j+1)) * (-2*(j+1) + 1)), [0, inf])
def B(x):
    x = int(x); return float(mpf(x) / 2 + lz0 + lzm1 / x + triv(x))
PB = 100_000
P = primes[primes <= PB]
R = np.array([(psi[p - 1] - S1[p - 1] / p) - B(int(p)) for p in P])   # R(p) = A(p) − B(p), A(p) avec n < p strict
dem = np.diff(R)                                                  # demandes des écarts [p_n, p_{n+1}]
sgn = np.sign(dem); changes = int(np.sum(sgn[1:] != sgn[:-1]))
log("Volet 2 (tentative A) : %d points de rencontre (premiers ≤ %d) ; R(p_1) = %.6f" % (len(P), PB, R[0]))
log("  demandes : %d positives, %d négatives, %d changements de signe ; somme télescopée = R(p_N) − R(p_1) = %.6f (vérif : %.6f)"
    % (int(np.sum(dem > 0)), int(np.sum(dem < 0)), changes, np.sum(dem), R[-1] - R[0]))
for th in [0.5, 0.6, 0.7]:
    v = np.abs(R) / P.astype(float) ** th; k = int(np.argmax(v))
    log("  θ = %.1f : max |R(p)|/p^θ = %.5f en p = %d ; valeur au dernier point p = %d : %.5f" % (th, v[k], P[k], P[-1], v[-1]))
log("  lecture A : la somme partielle des demandes aux rencontres EST le reste lissé (identité télescopique) ; aucune loi "
    "d'annulation n'est lue ici autrement que par la valeur du reste lui-même.")

# ---------- Volet 3 — tentative B minimale ----------
h = hashlib.sha256(open(zfile, 'rb').read()).hexdigest()
ref = open(zfile + '.sha256').read().split()[0]; assert h == ref, ('SHA-256 mismatch', h, ref)
T = np.loadtxt(zfile, dtype=np.float64); assert len(T) == 2001052
log("Volet 3 (tentative B) : zéros Odlyzko chargés (sha256 ok), N = %d, T_max = %.3f" % (len(T), T[-1]))
Pb = primes
idx = [614, 615, 616, 617, 618, 619]
def raw_true_avg(p):   # (ψ(p−) + ψ(p+))/2 − fond brut en p
    return (psi[p] + psi[p - 1]) / 2 - (p - math.log(2 * math.pi) - 0.5 * math.log(1 - p ** -2.0))
# paire synthétique : β = 0.6 à une hauteur jamais ON (milieu de deux hauteurs consécutives autour de 1000)
k0 = int(np.searchsorted(T, 1000.0)); Tp = 0.5 * (T[k0] + T[k0 + 1]); beta = 0.6
log("  paire synthétique : β = %.1f, T = %.6f (milieu des hauteurs ON %.6f et %.6f)" % (beta, Tp, T[k0], T[k0 + 1]))
rows = []
for n in idx:
    p = int(Pb[n + 1]); lp = math.log(p)
    cut = math.pi * p
    sel = T[T < cut]
    rho = 0.5 + 1j * sel
    head = float(np.sum(2 * np.real(np.exp(rho * lp) / rho)))   # Σ_{|γ|<πp} x^ρ/ρ (zéros sur la ligne)
    true_sum = -raw_true_avg(p)                                  # Σ_ρ x^ρ/ρ = fond brut − ψ (moyenne des deux côtés)
    tail = true_sum - head
    pair = 0.0
    for b in (beta, 1 - beta):
        rz = b + 1j * Tp; pair += float(2 * np.real(np.exp(rz * lp) / rz))
    rows.append((n, p, len(sel), head, true_sum, tail, pair))
log("  n | p_{n+1} | zéros tête (γ<πp) | tête | somme vraie (crible) | queue | dépôt brut paire")
for row in rows:
    log("  %d | %d | %d | %+.4f | %+.4f | %+.4f | %+.4f" % row)
for a, b in zip(rows[:-1], rows[1:]):
    log("  pas de la paire entre p = %d et %d : %.4f ; (p'/p)^β = %.4f ; pas de la tête : %+.4f ; pas de la queue : %+.4f"
        % (a[1], b[1], b[6] - a[6], (b[1] / a[1]) ** beta, b[3] - a[3], b[5] - a[5]))
log("  lecture B : la paire est dans la tête à chaque rencontre ; son pas est lu par β ; rien ici ne contraint la tête "
    "ON à l'absorber ou non autrement que par la constance par membre (⟺ RH). Critère d'échec déclaré : B morte.")
log("terminé en %.1f s" % (time.time() - t0))

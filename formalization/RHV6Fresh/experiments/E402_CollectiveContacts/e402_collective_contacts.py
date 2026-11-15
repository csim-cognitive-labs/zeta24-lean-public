# E402 — Reconstruction collective par les contacts (mission R9, §19.30). Protocole pré-enregistré en §19.29.5 et README.
# Usage : python3 -I e402_collective_contacts.py <zeros_file> <prime_bound> <outdir>
# Borné : < 5 min (numpy ; 2 001 052 zéros × 1229 premiers). Aucune sortie fabriquée : tout est calculé ici.
import sys, os, hashlib, time, math
import numpy as np
from mpmath import mp, mpf, mpc, zeta, log as mlog, atan as matan, pi as mpi, quad, inf, nsum, exp as mexp

t0 = time.time()
zfile, PB, outdir = sys.argv[1], int(sys.argv[2]), sys.argv[3]
os.makedirs(outdir, exist_ok=True)
mp.dps = 30

# ---------- 0. Provenance ----------
h = hashlib.sha256(open(zfile, 'rb').read()).hexdigest()
ref = open(zfile + '.sha256').read().split()[0]
assert h == ref, ('SHA-256 mismatch', h, ref)
T = np.loadtxt(zfile, dtype=np.float64)
NZ = len(T); assert NZ == 2001052 and np.all(np.diff(T) > 0)
Tmax = float(T[-1])
log_prov = ["zeros: %s" % zfile, "sha256: %s (== fichier .sha256)" % h, "N zéros: %d ; T_1 = %.9f ; T_max = %.9f" % (NZ, T[0], Tmax),
            "hypothèse de données : hauteurs des zéros connus, posés sur la ligne (β = 1/2) ; elles ne certifient pas l'absence de zéros OFF"]

# ---------- 1. Premiers, Λ, demande première exacte A(x) = Σ_{m<x} Λ(m)(1 − m/x) ----------
def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
Pall = sieve(2 * PB)
P = [p for p in Pall if p <= PB]; P.append(Pall[len(P)])   # dernier écart : [p_max≤PB, premier suivant]
NP = len(P); NG = NP - 1
Lam = np.zeros(P[-1] + 2)
for p in Pall:
    q = p
    while q <= P[-1] + 1: Lam[q] = math.log(p); q *= p
m = np.arange(len(Lam))
S0 = np.cumsum(Lam); S1 = np.cumsum(Lam * m)            # S0[x] = Σ_{m≤x} Λ
def A(x):   # Σ_{m<x} Λ(m)(1 − m/x), x entier premier : m < x ⇔ m ≤ x−1
    return S0[x-1] - S1[x-1] / x
# jumeau mpmath de A pour les 3 écarts choisis plus bas
def A_mp(x):
    return sum(mpf(Lam[k]) * (1 - mpf(int(k)) / x) for k in range(2, x) if Lam[k] != 0)

# ---------- 2. Fond B(x) = x/2 − ζ'/ζ(0) + (ζ'/ζ)(−1)/x + Σ_j −x^{s_j}/(s_j(s_j+1)) (formule E401, aucune autre) ----------
lz0 = -(zeta(0, derivative=1) / zeta(0)); lzm1 = zeta(-1, derivative=1) / zeta(-1)
def triv(x):  # Σ_{j≥0} −x^{−2(j+1)}/((−2(j+1))(−2(j+1)+1))
    x = mpf(x); return nsum(lambda j: -(x ** (-2*(j+1))) / ((-2*(j+1)) * (-2*(j+1) + 1)), [0, inf])
def B(x): return float(mpf(x) / 2 + lz0 + lzm1 / x + triv(x))
Bv = np.array([B(p) for p in P]); Av = np.array([A(p) for p in P])
Pf = np.array(P, dtype=np.float64); logP = np.log(Pf)
ell = np.diff(logP)                                     # ℓ_n = log p_{n+1} − log p_n
Dn = np.diff(Av); Bn = np.diff(Bv); Zn = Dn - Bn       # Z_n = D_n − B_n = demande à reconstruire par les zéros

# ---------- 3. Sommes zéro par premier : F(p) = Σ_{tous zéros} p^ρ/(ρ(ρ+1)), ρ = 1/2 + iT ----------
rho = 0.5 + 1j * T; W = 1.0 / (rho * (rho + 1.0))     # poids lissés
F = np.zeros(NP, dtype=np.complex128)
for i, p in enumerate(P):
    F[i] = np.sqrt(p) * np.sum(np.exp(1j * (T * logP[i])) * W)
# contribution complexe d'un zéro à l'écart n : c_ρ(n) = −(b^ρ − a^ρ)/(ρ(ρ+1)) ; demande = 2 Re Σ c (conjugués)
Full = -(F[1:] - F[:-1])                                # Σ_{tous zéros} c_ρ(n)

# ---------- 4. Foule / queue par écart ----------
Tseuil = math.pi / ell
K = np.searchsorted(T, Tseuil, side='right')           # taille de la foule : #{T_ρ ≤ π/ℓ}
assert K.max() < NZ, "foule hors données"
Crowd = np.zeros(NG, dtype=np.complex128); CrowdAbs = np.zeros(NG)
n_contact = np.zeros(NG, dtype=int); quart = np.zeros((NG, 4), dtype=int); exact_meet = np.zeros(NG, dtype=int)
phi_all = np.arctan(T / 0.5)                           # phase de contact φ = arctan(T/β), β = 1/2
for n in range(NG):
    k = K[n]; Tk = T[:k]; r = rho[:k]; w = W[:k]
    c = -(np.exp(r * logP[n+1]) - np.exp(r * logP[n])) * w
    Crowd[n] = c.sum(); CrowdAbs[n] = np.abs(c).sum()
    th_in = Tk * logP[n] - phi_all[:k]; th_out = Tk * logP[n+1] - phi_all[:k]
    crossed = np.floor(th_out / math.pi) - np.floor(th_in / math.pi)
    if k > 0: assert crossed.max() <= 1 and crossed.min() >= 0   # foule : au plus un contact par écart (ℓ ≤ pas)
    n_contact[n] = int(crossed.sum())
    has = crossed == 1
    kk = np.floor(th_out[has] / math.pi)
    logC = (phi_all[:k][has] + kk * math.pi) / Tk[has]   # log C_k du contact traversé
    off = (logP[n+1] - logC) / ell[n]                     # décalage à la rencontre (fraction de l'écart, 0 = rencontre)
    quart[n] = np.histogram(off, bins=[-1e-12, 0.25, 0.5, 0.75, 1.0 + 1e-12])[0]
    exact_meet[n] = int(np.sum(np.abs(logP[n+1] - logC) < 1e-12))
Tail = Full - Crowd
Rn = Zn - 2 * Crowd.real - 2 * Tail.real               # résidu de reconstruction (troncature à T_max)

# ---------- 5. Borne de troncature indépendante du résidu : Σ_{γ>Tmax} 1/γ² via N(T) ≤ N_up(T) (Trudgian 2014) ----------
def N_up(t):
    t = mpf(t); return t / (2 * mpi) * mlog(t / (2 * mpi * mexp(1))) + mpf(7) / 8 + mpf('0.112') * mlog(t) + mpf('0.278') * mlog(mlog(t)) + mpf('2.510')
sigma = float(-mpf(NZ) / mpf(Tmax) ** 2 + 2 * quad(lambda t: N_up(t) / t ** 3, [Tmax, inf]))
eps_uncond = 2 * (Pf[1:] + Pf[:-1]) * sigma            # |x^ρ| ≤ x (β < 1), toute position radiale de la queue
eps_online = 2 * (np.sqrt(Pf[1:]) + np.sqrt(Pf[:-1])) * sigma

# ---------- 6. Transitions de composition ----------
dK = np.diff(K)                                        # variation de la foule entre écarts consécutifs (fenêtre d'un ensemble fixe)

# ---------- 7. Jumeaux déterministes ----------
tw = []
# 7a. contre E401 (demande exacte, dps 30) sur les 168 premiers écarts
e401 = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'E401_ThreeTowersRegister', 'e401_register_dps30.txt')
if os.path.exists(e401):
    dem = []
    for line in open(e401):
        if line.startswith('#'): continue
        parts = line.split('|'); dem.append(float(parts[7].strip()))
    d = max(abs(dem[i] - Zn[i]) for i in range(min(168, len(dem))))
    tw.append("E401 (dps 30) contre Z_n flottant, 168 écarts : max |Δ| = %.3e" % d)
# 7b. télescopage : Σ_n c_ρ(n) = −(F_ρ(p_last) − F_ρ(p_0)) pour les 100 premiers zéros
r100 = rho[:100]; w100 = W[:100]
tele = sum(-(np.exp(r100 * logP[n+1]) - np.exp(r100 * logP[n])) * w100 for n in range(NG))
tele_ref = -(np.exp(r100 * logP[-1]) - np.exp(r100 * logP[0])) * w100
tw.append("télescopage (100 zéros, %d écarts) : max |Σ_n c − (F(b_N) − F(a_0))| = %.3e" % (NG, np.abs(tele - tele_ref).max()))
# 7c. identités compilées sur l'oscillateur unitaire pour toute la foule des 3 écarts choisis, à deux précisions
chosen = [int(np.argmax(K > 0)), NG // 2, NG - 1]   # premier écart à foule non vide, écart médian, dernier écart
empty_crowd = int((K == 0).sum())
for n in chosen:
    k = K[n]; Tk = T[:k]
    u = (np.exp(1j * Tk * logP[n+1]) - np.exp(1j * Tk * logP[n])) / (1j * Tk)        # gapTerm(iT, a, b)
    nu = np.abs(u); formula = 2 * np.abs(np.sin(Tk * ell[n] / 2)) / Tk
    nm = max(abs(float(2 * abs(mp.sin(mpf(float(Tk[j])) * mpf(float(ell[n])) / 2)) / mpf(float(Tk[j]))) - nu[j]) for j in range(min(k, 200)))
    tw.append("écart n=%d (foule %d) : |u| = 2|sin(Tℓ/2)|/T max écart flottant %.2e, mpmath(200 premiers) %.2e ; plateau |u| ≤ ℓ : %s ; enveloppe |u| ≤ 2/T : %s"
              % (n, k, np.abs(nu - formula).max(), nm, bool(np.all(nu <= ell[n] * (1 + 1e-12))), bool(np.all(nu <= 2 / Tk * (1 + 1e-12)))))
# 7d. somme de foule des 3 écarts choisis recalculée en mpmath (dps 30) sur les mêmes hauteurs
for n in chosen:
    k = K[n]; s = mpc(0)
    for j in range(k):
        r = mpc(mpf('0.5'), mpf(float(T[j])))
        s += -(mexp(r * mlog(P[n+1])) - mexp(r * mlog(P[n]))) / (r * (r + 1))
    tw.append("foule n=%d : Σ c mpmath − numpy = %.2e ; A(x) mpmath − flottant = %.2e" % (n, abs(complex(s) - Crowd[n]), abs(float(A_mp(P[n+1]) - A_mp(P[n])) - Dn[n])))

# ---------- 8. Dérive : contacts et contributions, deux coordonnées séparées (10 premiers zéros, 3 écarts) ----------
drift = []
for n in chosen:
    a, b = logP[n], logP[n+1]
    for j in range(10):
        r = rho[j]; Tj = T[j]; be = 0.5
        def G(x): return np.exp(r * x) / (r * (r + 1))
        dG = lambda x: np.exp(r * x) * (x / (r * (r + 1)) - (2 * r + 1) / (r * (r + 1)) ** 2)
        dc_drho = -(dG(b) - dG(a))                       # dc/dρ ; ∂c/∂β = dc/dρ ; ∂c/∂T = i·dc/dρ
        c = -(G(b) - G(a))
        phi = math.atan(Tj / be); th_out = Tj * b - phi; kk = math.floor(th_out / math.pi)
        u_k = (phi + kk * math.pi) / Tj
        du_dbeta = -1.0 / (be ** 2 + Tj ** 2); du_dT = be / (Tj * (be ** 2 + Tj ** 2)) - u_k / Tj
        drift.append((n, j + 1, Tj, c, dc_drho, 1j * dc_drho, kk, u_k, du_dbeta, du_dT))

# ---------- 9. Synthétique SÉPARÉ : paire β* = 0.3 / 0.7 à T* = milieu entre les zéros 2000 et 2001 (hauteur d'aucun zéro réel) ----------
Tstar = 0.5 * (T[1999] + T[2000]); assert np.min(np.abs(T - Tstar)) > 1e-3
syn = []
for bs in (0.3, 0.7):
    r = bs + 1j * Tstar
    cs = -(np.exp(r * logP[1:]) - np.exp(r * logP[:-1])) / (r * (r + 1))
    syn.append(cs)
cpair = syn[0] + syn[1]
inside = Tseuil >= Tstar                                 # écarts dont la foule contient la paire
shift = (math.atan(Tstar / 0.7) - math.atan(Tstar / 0.3)) / Tstar
Rsyn = Rn - 2 * cpair.real                               # ce que le reste devrait absorber si la paire existait (contrôle)

# ---------- 10. Sorties ----------
with open(os.path.join(outdir, 'e402_per_gap.txt'), 'w') as f:
    f.write("# n p_n p_{n+1} ell D_n B_n Z_n T_seuil K_n 2Re(S_foule) Im(S_foule) Σ|c_foule| 2Re(S_queue) R_n eps_uncond eps_online nb_contacts_foule q1 q2 q3 q4 rencontres_exactes dK\n")
    for n in range(NG):
        f.write("%d %d %d %.9e %.12e %.12e %.12e %.6e %d %.12e %.6e %.6e %.12e %.6e %.3e %.3e %d %d %d %d %d %d %d\n" % (
            n, P[n], P[n+1], ell[n], Dn[n], Bn[n], Zn[n], Tseuil[n], K[n], 2*Crowd[n].real, Crowd[n].imag, CrowdAbs[n], 2*Tail[n].real,
            Rn[n], eps_uncond[n], eps_online[n], n_contact[n], *quart[n], exact_meet[n], (dK[n-1] if n > 0 else 0)))
with open(os.path.join(outdir, 'e402_members_chosen_gaps.txt'), 'w') as f:
    f.write("# écarts choisis : membres de la foule (40 premiers) ; colonnes : n rang T phi theta_in theta_out contacts k logC_k decalage_rencontre Re(c) Im(c) |c|\n")
    for n in chosen:
        k = min(K[n], 40)
        for j in range(k):
            Tj = T[j]; phi = phi_all[j]; thi = Tj * logP[n] - phi; tho = Tj * logP[n+1] - phi
            cr = math.floor(tho / math.pi) - math.floor(thi / math.pi)
            kk = math.floor(tho / math.pi); logC = (phi + kk * math.pi) / Tj
            c = -(np.exp(rho[j] * logP[n+1]) - np.exp(rho[j] * logP[n])) * W[j]
            f.write("%d %d %.9f %.9f %.6f %.6f %d %d %.9f %s %.6e %.6e %.6e\n" % (n, j+1, Tj, phi, thi, tho, cr, kk, logC,
                    ("%.4f" % ((logP[n+1]-logC)/ell[n])) if cr == 1 else "-", c.real, c.imag, abs(c)))
with open(os.path.join(outdir, 'e402_drift.txt'), 'w') as f:
    f.write("# dérive (3 écarts × 10 zéros) : n rang T Re(c) Im(c) |dc/dβ| |dc/dT| arg(dc/dβ) arg(dc/dT) k u_k du_k/dβ du_k/dT ; dpas/dβ = 0 exact\n")
    for (n, j, Tj, c, db, dT, kk, uk, dub, duT) in drift:
        f.write("%d %d %.6f %.6e %.6e %.6e %.6e %.4f %.4f %d %.9f %.6e %.6e\n" % (n, j, Tj, c.real, c.imag, abs(db), abs(dT), np.angle(db), np.angle(dT), kk, uk, dub, duT))
with open(os.path.join(outdir, 'e402_synthetic.txt'), 'w') as f:
    f.write("# SYNTHÉTIQUE, SÉPARÉ : paire β*=0.3/0.7, T* = %.9f (milieu des zéros 2000/2001 ; distance min à un zéro réel %.4e)\n" % (Tstar, np.min(np.abs(T - Tstar))))
    f.write("# décalage des contacts de la paire (log) : %.6e ; nombre d'écarts dont la foule contient la paire : %d / %d\n" % (shift, int(inside.sum()), NG))
    f.write("# n dans_foule 2Re(c_0.3) 2Re(c_0.7) 2Re(c_paire) |c_0.3| |c_0.7| R_n R_n_avec_paire\n")
    for n in range(NG):
        f.write("%d %d %.6e %.6e %.6e %.6e %.6e %.6e %.6e\n" % (n, int(inside[n]), 2*syn[0][n].real, 2*syn[1][n].real, 2*cpair[n].real, abs(syn[0][n]), abs(syn[1][n]), Rn[n], Rsyn[n]))

absR = np.abs(Rn)
with open(os.path.join(outdir, 'e402_summary.txt'), 'w') as f:
    f.write("E402 — exécution du %s ; durée %.1f s ; premiers ≤ %d (%d écarts, dernier [%d, %d])\n" % (time.strftime('%Y-%m-%d %H:%M:%S'), time.time() - t0, PB, NG, P[-2], P[-1]))
    for s in log_prov: f.write("provenance : " + s + "\n")
    f.write("constantes : −ζ'/ζ(0) = %s ; (ζ'/ζ)(−1) = %s\n" % (mp.nstr(lz0, 20), mp.nstr(lzm1, 20)))
    f.write("borne de queue : Σ_{γ>T_max} 1/γ² ≤ %.6e (N(T) ≤ N_up, Trudgian 2014 ; N(T_max) = %d exact)\n" % (sigma, NZ))
    f.write("foules : K_min = %d (n=%d) ; K_max = %d (n=%d) ; toutes dans les données (K_max < %d) ; écarts à foule VIDE (seuil π/ℓ < T_1) : %d (rangs %s)\n" % (K.min(), K.argmin(), K.max(), K.argmax(), NZ, empty_crowd, np.nonzero(K == 0)[0].tolist()))
    f.write("résidu R_n = Z_n − 2Re(S_foule + S_queue) : max |R_n| = %.3e (n=%d) ; médiane %.3e\n" % (absR.max(), absR.argmax(), np.median(absR)))
    f.write("écarts avec |R_n| ≤ eps_uncond : %d / %d ; |R_n| ≤ eps_online : %d / %d\n" % (int((absR <= eps_uncond).sum()), NG, int((absR <= eps_online).sum()), NG))
    f.write("eps_uncond : min %.3e max %.3e ; eps_online : min %.3e max %.3e\n" % (eps_uncond.min(), eps_uncond.max(), eps_online.min(), eps_online.max()))
    f.write("part de la foule : |2Re S_foule| / |Z_n| médiane %.4f ; |2Re S_queue|/|Z_n| médiane %.4f\n" % (np.median(np.abs(2*Crowd.real)/np.abs(Zn)), np.median(np.abs(2*Tail.real)/np.abs(Zn))))
    nz = CrowdAbs > 0
    f.write("part de phase (foule non vide) : |S_foule| / Σ|c| : min %.4f médiane %.4f max %.4f\n" % ((np.abs(Crowd[nz])/CrowdAbs[nz]).min(), np.median(np.abs(Crowd[nz])/CrowdAbs[nz]), (np.abs(Crowd[nz])/CrowdAbs[nz]).max()))
    f.write("contacts traversés par la foule : total %d ; écarts sans aucun contact de foule : %d ; rencontres exactes (contact = p_{n+1}) : %d\n" % (n_contact.sum(), int((n_contact == 0).sum()), exact_meet.sum()))
    f.write("quarts de l'écart où tombent les contacts de foule (depuis la rencontre) : %s\n" % quart.sum(axis=0).tolist())
    f.write("transitions : dK min %d max %d ; écarts où la foule grandit %d, rétrécit %d, constante %d\n" % (dK.min(), dK.max(), int((dK > 0).sum()), int((dK < 0).sum()), int((dK == 0).sum())))
    for s in tw: f.write("jumeau : " + s + "\n")
    f.write("SYNTHÉTIQUE (séparé) : T* = %.6f ; décalage contacts %.4e ; écarts contenant la paire dans la foule : %d ; max |2Re c_paire| sur ces écarts %.3e ; max |R_n avec paire| %.3e contre max |R_n| réel %.3e\n"
            % (Tstar, shift, int(inside.sum()), np.abs(2*cpair.real[inside]).max() if inside.any() else 0.0, np.abs(Rsyn[inside]).max() if inside.any() else 0.0, absR.max()))
    f.write("aucune conclusion sur β ; aucune comparaison à une moyenne ; aucun contact n'est un premier.\n")
print(open(os.path.join(outdir, 'e402_summary.txt')).read())

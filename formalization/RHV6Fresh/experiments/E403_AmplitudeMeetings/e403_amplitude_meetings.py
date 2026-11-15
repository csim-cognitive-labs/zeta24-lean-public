# E403 — Somme réelle des dépôts aux vrais points de rencontre, vraies amplitudes (pré-enregistré dans README.md).
# Usage : python3 -I e403_amplitude_meetings.py <zeros_file> <prime_bound> <outdir>
# Borné (< 5 min). Aucune sortie fabriquée : tout est calculé ici. Canal lissé compilé uniquement.
import sys, os, hashlib, time, math
import numpy as np
from mpmath import mp, mpf, mpc, zeta, log as mlog, quad, inf, nsum, exp as mexp, pi as mpi

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
prov = ["zeros: %s" % zfile, "sha256: %s (== .sha256)" % h, "N = %d ; T_1 = %.9f ; T_max = %.9f" % (NZ, T[0], Tmax),
        "hypothèse de données : hauteurs de zéros connus posés sur la ligne (β = 1/2) ; ne certifient pas l'absence de zéros OFF"]

# ---------- 1. Vrais écarts : premiers, Λ, demande exacte A(x) ----------
def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
Pall = sieve(2 * PB)
P = [p for p in Pall if p <= PB]; P.append(Pall[len(P)])
NP = len(P); NG = NP - 1
Lam = np.zeros(P[-1] + 2)
for p in Pall:
    q = p
    while q <= P[-1] + 1: Lam[q] = math.log(p); q *= p
m = np.arange(len(Lam)); S0 = np.cumsum(Lam); S1 = np.cumsum(Lam * m)
def A(x): return S0[x-1] - S1[x-1] / x
def A_mp(x): return sum(mpf(Lam[k]) * (1 - mpf(int(k)) / x) for k in range(2, x) if Lam[k] != 0)

# ---------- 2. Fond (formule E401/E402) ----------
lz0 = -(zeta(0, derivative=1) / zeta(0)); lzm1 = zeta(-1, derivative=1) / zeta(-1)
def triv(x):
    x = mpf(x); return nsum(lambda j: -(x ** (-2*(j+1))) / ((-2*(j+1)) * (-2*(j+1) + 1)), [0, inf])
def B(x): return float(mpf(x) / 2 + lz0 + lzm1 / x + triv(x))
Bv = np.array([B(p) for p in P]); Av = np.array([A(p) for p in P])
Pf = np.array(P, dtype=np.float64); logP = np.log(Pf); ell = np.diff(logP)
Dn = np.diff(Av); Bn = np.diff(Bv); Zn = Dn - Bn

# ---------- 3. Dépôts d_ρ(x) = −x^ρ/(ρ(ρ+1)) à chaque premier ; contributions c_ρ(n) ----------
rho = 0.5 + 1j * T; W = 1.0 / (rho * (rho + 1.0))
Dep = np.zeros(NP, dtype=np.complex128)           # Σ_ρ d_ρ(p) (tous zéros)
for i, p in enumerate(P):
    Dep[i] = -np.sqrt(p) * np.sum(np.exp(1j * (T * logP[i])) * W)
Full = Dep[1:] - Dep[:-1]                         # Σ_ρ c_ρ(n)
Rn = Zn - 2 * Full.real                           # résidu de l'identité réelle (troncature à T_max)

# ---------- 4. Foule par écart : somme signée, somme des amplitudes, contacts porteurs d'amplitude ----------
Tseuil = math.pi / ell
K = np.searchsorted(T, Tseuil, side='right'); assert K.max() < NZ
Crowd = np.zeros(NG, dtype=np.complex128); CrowdAbs = np.zeros(NG)
AmpMeet = np.zeros(NG)                            # Σ_foule |d_ρ(p_{n+1})| : amplitudes au point de rencontre
nc = np.zeros(NG, dtype=int); beta_read_max_err = np.zeros(NG)
phi_all = np.arctan(T / 0.5)
for n in range(NG):
    k = K[n]
    if k == 0: continue
    Tk = T[:k]; r = rho[:k]; w = W[:k]
    dpn1 = -np.exp(r * logP[n+1]) * w; dpn = -np.exp(r * logP[n]) * w
    c = dpn1 - dpn
    Crowd[n] = c.sum(); CrowdAbs[n] = np.abs(c).sum(); AmpMeet[n] = np.abs(dpn1).sum()
    th_in = Tk * logP[n] - phi_all[:k]; th_out = Tk * logP[n+1] - phi_all[:k]
    crossed = np.floor(th_out / math.pi) - np.floor(th_in / math.pi)
    assert crossed.max() <= 1 and crossed.min() >= 0
    has = crossed == 1; nc[n] = int(has.sum())
    if nc[n]:
        kk = np.floor(th_out[has] / math.pi)
        logC = (phi_all[:k][has] + kk * math.pi) / Tk[has]            # log C_k
        logC1 = (phi_all[:k][has] + (kk + 1) * math.pi) / Tk[has]     # log C_{k+1}
        A0 = np.exp(0.5 * logC) * np.abs(w[has]); A1 = np.exp(0.5 * logC1) * np.abs(w[has])
        beta_read = Tk[has] * np.log(A1 / A0) / math.pi
        beta_read_max_err[n] = np.abs(beta_read - 0.5).max()

# ---------- 5. Bornes de queue (comme E402) ----------
def N_up(t):
    t = mpf(t); return t / (2 * mpi) * mlog(t / (2 * mpi * mexp(1))) + mpf(7) / 8 + mpf('0.112') * mlog(t) + mpf('0.278') * mlog(mlog(t)) + mpf('2.510')
sigma = float(-mpf(NZ) / mpf(Tmax) ** 2 + 2 * quad(lambda t: N_up(t) / t ** 3, [Tmax, inf]))
eps_uncond = 2 * (Pf[1:] + Pf[:-1]) * sigma
eps_online = 2 * (np.sqrt(Pf[1:]) + np.sqrt(Pf[:-1])) * sigma

# ---------- 6. Jumeaux mpmath (3 écarts) ----------
chosen = [int(np.argmax(K > 0)), NG // 2, NG - 1]
tw = []
for n in chosen:
    k = K[n]; s = mpc(0); samp = mpf(0)
    for j in range(k):
        r = mpc(mpf('0.5'), mpf(float(T[j])))
        d1 = -mexp(r * mlog(P[n+1])) / (r * (r + 1)); d0 = -mexp(r * mlog(P[n])) / (r * (r + 1))
        s += d1 - d0; samp += abs(d1)
    tw.append("n=%d (foule %d) : Σc mpmath − numpy = %.2e ; Σ|d(p_{n+1})| mpmath − numpy = %.2e ; ΔA mpmath − flottant = %.2e"
              % (n, k, abs(complex(s) - Crowd[n]), abs(float(samp) - AmpMeet[n]), abs(float(A_mp(P[n+1]) - A_mp(P[n])) - Dn[n])))

# ---------- 7. Synthétique SÉPARÉ : le zéro ON de rang j0 est REMPLACÉ par une paire OFF à T* ----------
j0 = 1999                                         # rang 2000 (indice 0-based 1999)
Tstar = 0.5 * (T[1999] + T[2000]); assert np.min(np.abs(T - Tstar)) > 1e-3
def contrib(r):
    return (-np.exp(r * logP[1:]) + np.exp(r * logP[:-1])) / (r * (r + 1))
c_on = contrib(rho[j0]); c03 = contrib(0.3 + 1j * Tstar); c07 = contrib(0.7 + 1j * Tstar)
Delta = 2 * (c03 + c07 - c_on).real               # complément exigé par le remplacement
inside = Tseuil >= Tstar
amp_on = np.abs(np.exp(rho[j0] * logP[1:]) / (rho[j0] * (rho[j0] + 1)))
r03 = 0.3 + 1j * Tstar; r07 = 0.7 + 1j * Tstar
amp03 = np.abs(np.exp(r03 * logP[1:]) / (r03 * (r03 + 1))); amp07 = np.abs(np.exp(r07 * logP[1:]) / (r07 * (r07 + 1)))
slope = np.polyfit(logP[1:], np.log(amp07 / amp03), 1)[0]   # attendu 0,4 exactement
# lecture β sur les contacts synthétiques (premier contact de la paire dans chaque écart contenant la paire)
def beta_read_syn(bs):
    phi = math.atan(Tstar / bs); out = []
    for n in range(NG):
        tho = Tstar * logP[n+1] - phi; kk = math.floor(tho / math.pi)
        lC = (phi + kk * math.pi) / Tstar; lC1 = (phi + (kk + 1) * math.pi) / Tstar
        out.append(Tstar * math.log(math.exp(bs * lC1) / math.exp(bs * lC)) / math.pi)
    return np.array(out)
b03 = beta_read_syn(0.3); b07 = beta_read_syn(0.7)

# ---------- 8. Sorties ----------
absR = np.abs(Rn); nz = K > 0
with open(os.path.join(outdir, 'e403_per_gap.txt'), 'w') as f:
    f.write("# n p_n p_{n+1} ell Z_n 2Re(Σc_tous) R_n K_n 2Re(S_foule) Σ|c_foule| Σ|d_foule(p_{n+1})| nb_contacts_foule max|β_lue−0.5| eps_online eps_uncond\n")
    for n in range(NG):
        f.write("%d %d %d %.9e %.12e %.12e %.3e %d %.12e %.6e %.6e %d %.2e %.3e %.3e\n" % (
            n, P[n], P[n+1], ell[n], Zn[n], 2*Full[n].real, Rn[n], K[n], 2*Crowd[n].real, CrowdAbs[n], AmpMeet[n], nc[n], beta_read_max_err[n], eps_online[n], eps_uncond[n]))
with open(os.path.join(outdir, 'e403_contacts_chosen_gaps.txt'), 'w') as f:
    f.write("# contacts porteurs d'amplitude, écarts choisis, membres traversant un contact (40 premiers) : n rang T k logC_k A_k A_{k+1} A_{k+1}/A_k exp(βπ/T) β_lue |d(p_{n+1})|\n")
    for n in chosen:
        k = K[n]; cnt = 0
        for j in range(k):
            if cnt >= 40: break
            Tj = T[j]; phi = phi_all[j]; thi = Tj * logP[n] - phi; tho = Tj * logP[n+1] - phi
            if math.floor(tho / math.pi) - math.floor(thi / math.pi) != 1: continue
            kk = math.floor(tho / math.pi); lC = (phi + kk * math.pi) / Tj; lC1 = (phi + (kk + 1) * math.pi) / Tj
            A0 = math.exp(0.5 * lC) * abs(W[j]); A1 = math.exp(0.5 * lC1) * abs(W[j])
            f.write("%d %d %.9f %d %.9f %.6e %.6e %.9f %.9f %.9f %.6e\n" % (n, j+1, Tj, kk, lC, A0, A1, A1/A0, math.exp(0.5*math.pi/Tj), Tj*math.log(A1/A0)/math.pi, math.sqrt(P[n+1])*abs(W[j])))
            cnt += 1
with open(os.path.join(outdir, 'e403_synthetic.txt'), 'w') as f:
    f.write("# SYNTHÉTIQUE, SÉPARÉ : zéro ON de rang %d (T = %.9f) REMPLACÉ par la paire β* = 0.3/0.7 à T* = %.9f (hauteur d'aucun zéro ; distance min %.4e)\n" % (j0+1, T[j0], Tstar, np.min(np.abs(T - Tstar))))
    f.write("# pente de log(|d_0.7|/|d_0.3|) contre log p_{n+1} : %.12f (attendu 1−2β* = 0.4)\n" % slope)
    f.write("# n dans_foule 2Re(c_ON) 2Re(c_0.3) 2Re(c_0.7) Delta_n |R_n| |Delta|>|R_n| |Delta|>eps_online |Delta|>eps_uncond |d_ON(p_{n+1})| |d_0.3| |d_0.7| β_lue_0.3 β_lue_0.7\n")
    for n in range(NG):
        f.write("%d %d %.6e %.6e %.6e %.6e %.3e %d %d %d %.6e %.6e %.6e %.9f %.9f\n" % (n, int(inside[n]), 2*c_on[n].real, 2*c03[n].real, 2*c07[n].real, Delta[n], absR[n],
                int(abs(Delta[n]) > absR[n]), int(abs(Delta[n]) > eps_online[n]), int(abs(Delta[n]) > eps_uncond[n]), amp_on[n], amp03[n], amp07[n], b03[n], b07[n]))
with open(os.path.join(outdir, 'e403_summary.txt'), 'w') as f:
    f.write("E403 — exécution du %s ; durée %.1f s ; premiers ≤ %d (%d écarts, dernier [%d, %d])\n" % (time.strftime('%Y-%m-%d %H:%M:%S'), time.time() - t0, PB, NG, P[-2], P[-1]))
    for s in prov: f.write("provenance : " + s + "\n")
    f.write("1. identité réelle Z_n = 2Re Σ_ρ c_ρ(n) : max |R_n| = %.3e (n=%d), médiane %.3e ; |R_n| ≤ eps_online : %d/%d\n" % (absR.max(), absR.argmax(), np.median(absR), int((absR <= eps_online).sum()), NG))
    f.write("2. contacts porteurs d'amplitude (réel) : %d contacts de foule ; max |β_lue − 0.5| = %.2e (hypothèse de données, pas une mesure)\n" % (nc.sum(), beta_read_max_err.max()))
    f.write("   synthétique : β_lue(0.3) : min %.12f max %.12f ; β_lue(0.7) : min %.12f max %.12f\n" % (b03.min(), b03.max(), b07.min(), b07.max()))
    f.write("3. foule non vide (%d écarts) : |2Re S_foule| / Σ|c_foule| médiane %.4f ; Σ|d_foule(p_{n+1})| / |Z_n| médiane %.3f ; Σ|c_foule| / |Z_n| médiane %.3f\n" % (
        int(nz.sum()), np.median(np.abs(2*Crowd[nz].real)/CrowdAbs[nz]), np.median(AmpMeet[nz]/np.abs(Zn[nz])), np.median(CrowdAbs[nz]/np.abs(Zn[nz]))))
    f.write("4. synthétique (remplacement) : écarts avec paire dans la foule %d/%d ; |Δ_n| > |R_n| : %d/%d ; |Δ_n| > eps_online : %d/%d ; |Δ_n| > eps_uncond : %d/%d\n" % (
        int(inside.sum()), NG, int((np.abs(Delta) > absR).sum()), NG, int((np.abs(Delta) > eps_online).sum()), NG, int((np.abs(Delta) > eps_uncond).sum()), NG))
    f.write("   |Δ_n| : min %.3e max %.3e ; |Δ_n|/|R_n| max %.3e ; |d_0.7|/|d_0.3| : min %.3f max %.3f ; pente contre log p_{n+1} : %.12f\n" % (
        np.abs(Delta).min(), np.abs(Delta).max(), (np.abs(Delta)/absR).max(), (amp07/amp03).min(), (amp07/amp03).max(), slope))
    f.write("   amplitudes au dernier point de rencontre p=%d : ON %.3e ; 0.3 %.3e ; 0.7 %.3e\n" % (P[-1], amp_on[-1], amp03[-1], amp07[-1]))
    f.write("5. jumeaux mpmath (dps 30) :\n")
    for s in tw: f.write("   " + s + "\n")
    f.write("borne de queue : Σ_{γ>T_max} 1/γ² ≤ %.6e ; eps_online min %.3e max %.3e ; eps_uncond min %.3e max %.3e\n" % (sigma, eps_online.min(), eps_online.max(), eps_uncond.min(), eps_uncond.max()))
    f.write("Aucune conclusion sur β des vrais zéros.\n")
print("E403 terminé en %.1f s" % (time.time() - t0))

# E406–E411 — jumeaux numériques (pré-enregistrés dans README.md). Borné, réel, aucune sortie fabriquée.
# Usage : python3 -I e406_e411_raw_spectral_channel.py <zeros_file> <outdir>
import sys, os, hashlib, time, math
import numpy as np
from mpmath import mp, mpf, zeta, log as mlog, pi as mpi, nsum, inf

t0 = time.time()
zfile, outdir = sys.argv[1], sys.argv[2]
os.makedirs(outdir, exist_ok=True)
out = open(os.path.join(outdir, 'e406_e411_results.txt'), 'w')
def log(s):
    out.write(s + "\n"); out.flush(); print("[%6.1f s] %s" % (time.time() - t0, s), flush=True)

mp.dps = 30
# ---------- constantes de fond compilées (ZetaSmoothedZeroFormulaP5) ----------
c0 = -zeta(0, derivative=1) / zeta(0)          # −logDeriv ζ (0)
c1 = zeta(-1, derivative=1) / zeta(-1)         # logDeriv ζ (−1)
tau = nsum(lambda n: 1 / (n + 1) ** 2, [0, inf])   # trivialTailConstant (borne compilée, = π²/6)
def Ttriv(x):   # Σ' trivialZeroResidueTerm x n = −Σ_{k≥1} x^{−2k} / ((−2k)(−2k+1))
    x = mpf(x)
    return -nsum(lambda k: x ** (-2 * k) / ((-2 * k) * (-2 * k + 1)), [1, inf])
def B(x):       # smoothedZeroBackground x
    x = mpf(x)
    return x / 2 + c0 + c1 / x + Ttriv(x)
def bgStep(N):  # stepAt backgroundPrimitive N = (N+1)B(N+1) − N B(N)
    return (N + 1) * B(N + 1) - N * B(N)
def cellCorr(N):   # cellCorrection N = 1/2 + c0 + ((N+1)T(N+1) − N T(N))
    return mpf(1) / 2 + c0 + ((N + 1) * Ttriv(N + 1) - N * Ttriv(N))
cbc = mpf(1) / 2 + abs(c0) + 2 * tau       # cellBackgroundConstant
log("constantes : c0 = −logDeriv ζ(0) = %s ; c1 = logDeriv ζ(−1) = %s ; τ = %s ; cellBackgroundConstant = %s"
    % (mp.nstr(c0, 12), mp.nstr(c1, 12), mp.nstr(tau, 12), mp.nstr(cbc, 12)))

# ---------- zéros (réels, Odlyzko) ----------
h = hashlib.sha256(open(zfile, 'rb').read()).hexdigest()
ref = open(zfile + '.sha256').read().split()[0]; assert h == ref, ('SHA-256 mismatch', h, ref)
G = np.loadtxt(zfile, dtype=np.float64); assert len(G) == 2001052
G = np.sort(G); rho = 0.5 + 1j * G; den = rho * (rho + 1)
log("zéros : %d hauteurs (SHA-256 vérifié), γ_max = %.3f ; hauteurs posées sur la ligne (hypothèse de données), m = 1" % (len(G), G[-1]))

# ---------- crible ----------
X = 2_000_000
s = np.ones(X + 1, dtype=bool); s[:2] = False
for i in range(2, int(X ** 0.5) + 1):
    if s[i]: s[i*i::i] = False
primes = np.nonzero(s)[0]
Lam = np.zeros(X + 1)
for p in primes:
    q = p
    while q <= X:
        Lam[q] = math.log(p); q *= p
psi = np.cumsum(Lam)

def cell_primitive_terms(x):
    """termes de la primitive de cellule x·(−m x^ρ/(ρ(ρ+1))) par zéro (branche supérieure), triés par γ."""
    xr = float(x)
    return -(xr ** 1.5) * np.exp(1j * G * math.log(xr)) / den     # x · x^ρ /(ρ(ρ+1)), ρ = 1/2 + iγ
def cum_primitive(x):
    """primitive de cellule cumulée par seuil : les deux branches = 2·Re(branche supérieure)."""
    return 2.0 * np.cumsum(cell_primitive_terms(x)).real

Hs = [30.0, 100.0, 300.0, 594.0, 1000.0, 3000.0, 1e4, 3e4, 1e5, 3e5, float(G[-1])]
idx = [int(np.searchsorted(G, H, side='right')) for H in Hs]     # nb de zéros γ ≤ H (branche sup.)
P = [4547, 9587, 9931, 104729, 1000003]

log("")
log("=== Volet E406 : ψ(N) − N = spectralRemainder N + cellCorrection N (convention de cellule, 2 001 052 zéros) ===")
for p in P:
    for N in (p - 1, p):
        Zp1 = cum_primitive(N + 1)[-1]; Z0 = cum_primitive(N)[-1]
        spec = Zp1 - Z0                     # spectralRemainder N tronqué
        lhs = psi[N] - N
        corr = float(cellCorr(N))
        resid = lhs - (spec + corr)
        tailb = 2.0 * (N + 1) ** 1.5 * float(nsum(lambda k: 1 / (G[-1] + k) ** 2, [1, 1]))  # non utilisé : borne absolue inutile
        log("  N = %7d : ψ(N)−N = %+12.5f ; spectral(tronqué) + c(N) = %+12.5f ; résidu = %+.4e ; |c(N)| = %.6f ≤ %.6f : %s ; "
            "résolution π·N/γ_max = %.3f"
            % (N, lhs, spec + corr, resid, abs(corr), float(cbc), abs(corr) <= float(cbc), math.pi * N / G[-1]))

log("")
log("=== Volet E407/E408 : incrément du paquet bas à la rencontre p (N = p−1) contre sa borne compilée K(H) ===")
log("    (K(H) = nombre de zéros de hauteur ≤ H, deux branches, multiplicité 1 ; cassure = log p ; "
    "borne compilée du complément : log p − 1 − 4τ − K(H))")
for p in [4547, 9587, 104729]:
    N = p - 1
    C2 = cum_primitive(N + 2); C1 = cum_primitive(N + 1); C0 = cum_primitive(N)
    inc_low = (C2 - C1) - (C1 - C0)                       # packetIncrement(low H)(N) par seuil (cumulé)
    total_inc = Lam[N + 1] - float(bgStep(N + 1) - bgStep(N))   # remainderIncrement N, par l'identité arithmétique (exact)
    bb1 = float(bgStep(N + 1) - bgStep(N)) - 1.0
    log("  p = %d : log p = %.4f ; seconde différence du fond − 1 = %+.3e (borne 4τ = %.3f) ; "
        "remainderIncrement (identité) = %+.5f ; par les zéros (tronqué) = %+.5f"
        % (p, math.log(p), bb1, 4 * float(tau), total_inc, inc_low[-1]))
    floor_H = None
    for H, k in zip(Hs, idx):
        low = inc_low[k - 1] if k > 0 else 0.0
        K = 2 * k
        comp = total_inc - low            # packetIncrement(complément)(N) par l'identité (exact modulo troncature du bas)
        lb = math.log(p) - 1 - 4 * float(tau) - K
        log("    H = %9.1f : K(H) = %7d ; |incr. bas| = %9.4f (borne K : %s, quotient %.2e) ; incr. complément = %+9.4f ; "
            "borne compilée du complément = %+9.3f ; part de (log p − 1) portée au-dessus de H = %6.1f %%"
            % (H, K, abs(low), abs(low) <= K + 1e-9, abs(low) / max(K, 1), comp, lb, 100 * comp / (math.log(p) - 1)))
        if floor_H is None and K >= math.log(p) - 1 - 4 * float(tau):
            floor_H = H
    # plancher compilé exact : plus petit H tel que 2·#{γ ≤ H} ≥ log p − 1 − 4τ
    need = math.log(p) - 1 - 4 * float(tau)
    kneed = max(0, math.ceil(need / 2))
    Hfloor = G[kneed - 1] if kneed >= 1 else 0.0
    log("    plancher compilé (frequency_floor_of_low_realization) : K(H) ≥ %.3f dès H ≥ γ_%d = %.3f ; "
        "fréquence observée en E404 pour la cassure nette : ordre π·p = %.0f" % (need, kneed, Hfloor, math.pi * p))

log("")
log("=== Volet E411 (lecture seule) : ‖localPacket (low H)ᶜ p‖ / √p, le niveau du complément, par seuil ===")
for p in [4547, 9587, 104729]:
    Cp1 = cum_primitive(p + 1); Cp = cum_primitive(p)
    step_low = Cp1 - Cp                                   # localPacket(low H)(p) cumulé par seuil
    total_step = float((psi[p] - bgStep(p)))              # exactRemainder p = spectralRemainder p (identité, exact)
    line = "  p = %d : exactRemainder p = %+.4f (= ψ(p) − fond ; ψ(p)−p = %+.4f) ; " % (p, total_step, psi[p] - p)
    parts = []
    for H, k in zip(Hs, idx):
        low = step_low[k - 1] if k > 0 else 0.0
        parts.append("H=%g: bas %+.3f, compl/√p %+.4f" % (H, low, (total_step - low) / math.sqrt(p)))
    log(line); log("     " + " | ".join(parts))

log("")
log("Temps total : %.1f s. Aucune conclusion sur l'exposant : jumeau, pas preuve." % (time.time() - t0))
out.close()

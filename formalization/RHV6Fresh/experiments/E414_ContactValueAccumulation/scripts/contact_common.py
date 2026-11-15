# -*- coding: utf-8 -*-
"""Bibliothèque commune E414–E419 : Tours, contacts, canaux brut et intégré, accumulation signée.

Conventions (identiques aux modules Lean Terminal/ContactValueGeometry.lean …
Terminal/PrimeGapReconstruction.lean) :
  towerValue ρ x        = x^ρ/ρ                      (Tour géométrique)
  integratedTower ρ x   = x^ρ/(ρ(ρ+1))               (canal intégré compilé)
  contact C_k(β,T)      = exp((arctan(T/β) + kπ)/T)  (windingContact)
  ψ̂₁(x) = x·B(x) − x·Σ_ρ x^ρ/(ρ(ρ+1)),  B(x) = x/2 + c0 + c1/x + Ttriv(x),
          c0 = −ζ'/ζ(0) = −log 2π,  c1 = ζ'/ζ(−1),  Ttriv(x) = −Σ_{k≥1} x^{−2k}/((−2k)(−2k+1))
  ψ̂₀(x) = x − log 2π − ½ log(1 − x⁻²) − Σ_ρ x^ρ/ρ     (canal brut, prémisse RawExplicitFormulaAt)
Les sommes sur ρ parcourent les deux branches : pour une liste de ρ de partie imaginaire > 0,
Σ = 2·Re (famille stable par conjugaison, finite_contact_accumulation_real).
Données réelles : hauteurs d'Odlyzko posées sur la ligne (hypothèse de données, m = 1).
Les valeurs arithmétiques (Λ, premiers) ne sont fournies QUE par les fonctions marquées VALIDATION.
"""
import os, sys, hashlib, time, math
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.normpath(os.path.join(HERE, "..", "..", "data", "odlyzko_zeros6_2001052.txt"))
LOG2PI = math.log(2 * math.pi)
C0 = -LOG2PI                      # −logDeriv ζ(0)
C1 = 1.9850537244054112           # logDeriv ζ(−1) = ζ'(−1)/ζ(−1) (mpmath, 16 chiffres)
CHUNK = 262144

class Logger:
    def __init__(self, path):
        self.f = open(path, "a"); self.t0 = time.time()
    def __call__(self, s):
        line = "[%8.2fs] %s" % (time.time() - self.t0, s)
        print(line, flush=True); self.f.write(line + "\n"); self.f.flush()

def load_zeros(log=print):
    h = hashlib.sha256()
    with open(DATA, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    sha = h.hexdigest()
    exp = open(DATA + ".sha256").read().split()[0]
    assert sha == exp, "SHA-256 mismatch"
    G = np.loadtxt(DATA, dtype=np.float64)
    assert len(G) == 2001052 and np.all(np.diff(G) > 0)
    log("zéros : %d hauteurs, SHA-256 %s… vérifié, γ_max = %.6f" % (len(G), sha[:16], G[-1]))
    return G, sha

def ttriv(x):
    x = float(x); s = 0.0; k = 1
    while True:
        t = x ** (-2 * k) / ((-2 * k) * (-2 * k + 1)); s += t
        if abs(t) < 1e-18 or k > 200: break
        k += 1
    return -s

def background_psi1(x):
    """x·B(x) (fond de la primitive intégrée)."""
    return x * (x / 2 + C0 + C1 / x + ttriv(x))

def background_raw(x):
    return x - LOG2PI - 0.5 * math.log(1 - x ** -2)

def sum_integrated(x, beta, gam, cumulative=False):
    """Σ_ρ 2Re[x^ρ/(ρ(ρ+1))] sur ρ = β + iγ (γ > 0), par morceaux ; cumulative → tableau cumulé."""
    lx = math.log(x); out = np.empty(len(gam)) if cumulative else 0.0
    for i in range(0, len(gam), CHUNK):
        g = gam[i:i + CHUNK]; b = beta[i:i + CHUNK] if np.ndim(beta) else beta
        rho = b + 1j * g
        v = 2.0 * np.real(np.exp(rho * lx) / (rho * (rho + 1)))
        if cumulative: out[i:i + CHUNK] = v
        else: out += v.sum()
    return np.cumsum(out) if cumulative else out

def sum_raw(x, beta, gam, cumulative=False):
    """Σ_ρ 2Re[x^ρ/ρ]."""
    lx = math.log(x); out = np.empty(len(gam)) if cumulative else 0.0
    for i in range(0, len(gam), CHUNK):
        g = gam[i:i + CHUNK]; b = beta[i:i + CHUNK] if np.ndim(beta) else beta
        rho = b + 1j * g
        v = 2.0 * np.real(np.exp(rho * lx) / rho)
        if cumulative: out[i:i + CHUNK] = v
        else: out += v.sum()
    return np.cumsum(out) if cumulative else out

def psi1_hat(x, beta, gam, cumulative=False):
    return background_psi1(x) - x * sum_integrated(x, beta, gam, cumulative)

def psi0_hat(x, beta, gam, cumulative=False):
    return background_raw(x) - sum_raw(x, beta, gam, cumulative)

# ---- contacts d'une Tour (β, T) ----
def phase(beta, T): return math.atan2(T, beta)   # arctan(T/β), β > 0
def contacts_in(beta, T, a, x):
    """Indices k et positions C_k dans [a, x]."""
    ph = phase(beta, T)
    kmin = math.ceil((T * math.log(a) - ph) / math.pi)
    kmax = math.floor((T * math.log(x) - ph) / math.pi)
    k = np.arange(kmin, kmax + 1, dtype=np.float64)
    return k, np.exp((ph + k * math.pi) / T)

def tower_value(rho, x):  return x ** rho / rho
def integrated_tower(rho, x): return x ** rho / (rho * (rho + 1))

def accumulate_one(rho, F, a, x):
    """A_ρ(a,x) = bord initial + Σ_k [F(C_{k+1}) − F(C_k)] + bord final, valeurs complexes.
    Retourne (accumulation, nombre de contacts, somme des modules des variations)."""
    k, C = contacts_in(rho.real, rho.imag, a, x)
    if len(C) == 0:
        v = F(rho, x) - F(rho, a); return v, 0, abs(v)
    FC = F(rho, C)
    V = FC[1:] - FC[:-1]
    acc = (FC[0] - F(rho, a)) + V.sum() + (F(rho, x) - FC[-1])
    return acc, len(C), np.abs(V).sum() + abs(FC[0] - F(rho, a)) + abs(F(rho, x) - FC[-1])

# ---- VALIDATION seulement (jamais utilisé dans une reconstruction) ----
def sieve_lambda(nmax):
    """VALIDATION : Λ(n) pour n ≤ nmax, et indicatrice des premiers."""
    isp = np.ones(nmax + 1, dtype=bool); isp[:2] = False
    for i in range(2, int(nmax ** 0.5) + 1):
        if isp[i]: isp[i * i::i] = False
    lam = np.zeros(nmax + 1)
    for p in np.nonzero(isp)[0]:
        q = p
        while q <= nmax:
            lam[q] = math.log(p); q *= p
    return lam, isp

def admissible_values(n):
    """Valeurs admissibles de Λ(n) sans données arithmétiques : 0, log n, et log n / k pour tout
    k ≥ 2 tel que n soit une puissance k-ième exacte (test sur n seul, pas sur les premiers)."""
    vals = [0.0, math.log(n)]
    k = 2
    while 2 ** k <= n:
        r = round(n ** (1.0 / k))
        for rr in (r - 1, r, r + 1):
            if rr >= 2 and rr ** k == n:
                vals.append(math.log(n) / k)
        k += 1
    return sorted(set(vals))

def classify(n, lam_hat):
    """Règle pré-enregistrée : valeur admissible la plus proche. Retourne (valeur, étiquette)."""
    vals = admissible_values(n)
    v = min(vals, key=lambda t: abs(t - lam_hat))
    if v == 0.0: lab = "none"
    elif abs(v - math.log(n)) < 1e-12: lab = "prime"
    else: lab = "power"
    return v, lab

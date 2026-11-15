#!/usr/bin/env python3
"""E475 — jumeau déterministe pré-enregistré : M1 premier partagé, M2 parts imposées des deux membres du raccord canonique à
l'écart ⟨n⟩ contre le transport, M3 sensibilité radiale sur une paire fictive. Définitions compilées reproduites (README)."""
import json, math, os, time, itertools, cmath
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = os.path.join(HERE, "..", "data", "odlyzko_zeros6_2001052.txt")
t0 = time.time()
NR = 2000                       # raccords n = 0..NR-1
def log(m): print(f"[{time.time()-t0:7.2f}s] {m}", flush=True)
# premiers : fnPrimeAtRank 0 = 2
lim = 40000
sieve = np.ones(lim, dtype=bool); sieve[:2] = False
for i in range(2, int(lim**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
P = np.nonzero(sieve)[0]; assert P.size > NR + 2
def fnPrimeAtRank(r): return int(P[r])
with open(ZEROS) as f:
    gam = [float(l.split()[0]) for l in itertools.islice(f, NR + 1)]
log(f"zéros lus : {len(gam)} ; γ_1 = {gam[0]}")
def canonicalMember(n): return (0.5, gam[n])          # (β, T), β = 1/2 sur les données d'Odlyzko
def occurrence(n): return fnPrimeAtRank(n)             # occurrence = fnPrimeAtRank (index)
def expectedMinimumPrime(n): return fnPrimeAtRank(n+1) # = fnPrimeSuccessor index
def meetingPoint(n): return fnPrimeAtRank(n+1)         # ⟨n⟩.upper
def memberJoint(beta, T, x, m=1.0):
    rho = complex(beta, T)
    N = abs(rho) * abs(rho + 1)
    theta = math.atan(T/beta) + math.atan(T/(beta+1))
    return -m * (x**beta / N) * cmath.exp(1j*(T*math.log(x) - theta))
def imposedShare(beta, T, n): return memberJoint(beta, T, meetingPoint(n)) - memberJoint(beta, T, occurrence(n))
def energyRatio(e, l, q):   # ‖zeroTerm l q‖/‖zeroTerm e q‖ = q^{β_l−β_e} ‖ρ_e‖/‖ρ_l‖
    return q**(l[0]-e[0]) * abs(complex(*e)) / abs(complex(*l))
def Phi(T, n):
    a, b = occurrence(n), meetingPoint(n)
    return abs(math.sqrt(b)*cmath.exp(1j*T*math.log(b)) - math.sqrt(a)*cmath.exp(1j*T*math.log(a)))
OUT = {"NR": NR, "hypothese_calcul": "zéros d'Odlyzko sur la ligne, multiplicité 1 (jamais une prémisse Lean)"}
# ---- M1
m1_ok = all(expectedMinimumPrime(n) == occurrence(n+1) == meetingPoint(n) for n in range(NR))
OUT["M1"] = dict(exact=m1_ok, exemples=[(n, occurrence(n), expectedMinimumPrime(n), meetingPoint(n)) for n in range(10)])
log(f"M1 exact sur {NR} raccords : {m1_ok}")
# ---- M2
rows = []; ident_res = 0.0
for n in range(NR):
    e, l = canonicalMember(n), canonicalMember(n+1)
    se, sl = imposedShare(*e, n), imposedShare(*l, n)
    for (b, T), s in ((e, se), (l, sl)):
        N = abs(complex(b, T)) * abs(complex(b, T) + 1)
        ident_res = max(ident_res, abs(abs(s) - Phi(T, n)/N) / max(abs(s), 1e-300))
    r = abs(sl)/abs(se); E = energyRatio(e, l, meetingPoint(n))
    fac_norm = abs(complex(*e)+1)/abs(complex(*l)+1); fac_phi = Phi(l[1], n)/Phi(e[1], n)
    rows.append(dict(n=n, p_n=occurrence(n), M=meetingPoint(n), T_e=e[1], T_l=l[1], abs_se=abs(se), abs_sl=abs(sl),
                     r=r, E=E, r_sur_E=r/E, fac_norme=fac_norm, fac_phase=fac_phi, Phi_e=Phi(e[1], n), Phi_l=Phi(l[1], n)))
dev10 = [abs(x["r_sur_E"]-1) for x in rows[:10]]
m2_ok = max(dev10) < 1e-6
fp = np.array([x["fac_phase"] for x in rows]); rE = np.array([x["r_sur_E"] for x in rows])
tranches = []
for a in range(0, NR, 200):
    seg = fp[a:a+200]; segr = rE[a:a+200]
    tranches.append(dict(n_de=a, n_a=a+199, fac_phase_mediane=float(np.median(seg)), q1=float(np.quantile(seg, .25)),
                         q3=float(np.quantile(seg, .75)), min=float(seg.min()), max=float(seg.max()),
                         r_sur_E_mediane=float(np.median(segr)), r_sur_E_min=float(segr.min()), r_sur_E_max=float(segr.max())))
OUT["M2"] = dict(identite_residu_max=ident_res, test_1e6_dix_premiers=m2_ok, dix_premiers=rows[:10], tranches=tranches,
                 r_sur_E_global=dict(mediane=float(np.median(rE)), min=float(rE.min()), max=float(rE.max())),
                 fraction_r_sur_E_sup_1=float(np.mean(rE > 1)))
log(f"M2 identité {ident_res:.1e} ; test 1e-6 : {m2_ok} ; r/E dix premiers : {[round(x['r_sur_E'],4) for x in rows[:10]]}")
log(f"M2 fac_phase médiane globale {np.median(fp):.4f}, min {fp.min():.4f}, max {fp.max():.4f} ; r/E médiane {np.median(rE):.4f}")
# ---- M3
m3 = []
for n in range(10):
    e, l = canonicalMember(n), canonicalMember(n+1); se = imposedShare(*e, n)
    ref = None; row = dict(n=n, M=meetingPoint(n))
    for beta in (0.30, 0.40, 0.45, 0.50):
        pair = (memberJoint(beta, l[1], meetingPoint(n)) - memberJoint(beta, l[1], occurrence(n))
                + memberJoint(1-beta, l[1], meetingPoint(n)) - memberJoint(1-beta, l[1], occurrence(n)))
        val = abs(pair)/abs(se)
        if beta == 0.50: ref = val
        row[f"beta_{beta:.2f}"] = val
    for beta in (0.30, 0.40, 0.45):
        row[f"variation_rel_{beta:.2f}"] = abs(row[f"beta_{beta:.2f}"] - row["beta_0.50"]) / row["beta_0.50"]
    row["ref_2sl_check"] = abs(row["beta_0.50"] - 2*abs(imposedShare(*l, n))/abs(se)) / row["beta_0.50"]
    m3.append(row)
sens = max(x["variation_rel_0.40"] for x in m3) > 1e-3
OUT["M3"] = dict(sensible=sens, lignes=m3)
log(f"M3 sensible (β=0,40 > 1e-3) : {sens} ; variations β=0,40 : {[round(x['variation_rel_0.40'],4) for x in m3]}")
OUT["verdict"] = "A" if (m1_ok and m2_ok and sens) else ("B" if m1_ok else "C")
OUT["duree_s"] = time.time()-t0
json.dump(OUT, open(os.path.join(HERE, "twin_results.json"), "w"), indent=1, default=float)
log(f"verdict {OUT['verdict']} ; écrit twin_results.json")

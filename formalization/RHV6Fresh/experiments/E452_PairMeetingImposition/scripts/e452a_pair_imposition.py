#!/usr/bin/env python3
"""E452 (a) — K2b : ce que la rencontre impose aux deux termes de la paire au même premier. H1 mot exact du miroir
k* = k + ⌊f + δ/π⌋ ; H2 |s| ≤ 1 ; H3 même signe ⟺ s = 0 ; H4 |v+v*| = | |v| + (−1)^s |v*| | ; H5 |v| − |v*| ≤ |v+v*| ;
H6 non-compensation |v+v*| > |v_dom|/2 au-delà d'un rang ; H7 ligne v* = v. 18 couples OFF témoins + 6 couples ligne,
10^5 premiers ≤ 10^7 (graine 452). Observation sans loi : part des premiers à mots décalés contre |δ|/π."""
import os, sys, json, math, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e452a.log"))
G, sha = load_zeros(lg)
N = 10**7
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
P = np.nonzero(sieve)[0].astype(np.float64)
rng = np.random.default_rng(452)
S = np.sort(rng.choice(P, 100000, replace=False))
lg(f"premiers ≤ 10^7 : {len(P)} ; échantillon {len(S)} (graine 452)")

def word(beta, T, x):
    phi = math.atan2(T, beta)
    s = (T*np.log(x) - phi)/math.pi
    k = np.floor(s); f = s - k
    C = np.exp((phi + k*math.pi)/T)
    v = ((-1.0)**k) * C**beta / math.hypot(beta, T)
    return k.astype(np.int64), f, v

TOL = 1e-12
def check(beta, T, label):
    kb, fb, vb = word(beta, T, S)
    km, fm, vm = word(1-beta, T, S)
    delta = math.atan(T/beta) - math.atan(T/(1-beta))
    s = np.floor(fb + delta/math.pi).astype(np.int64)
    h1 = int(np.sum(km != kb + s))
    h2 = int(np.sum(np.abs(s) > 1))
    same_sign = vb*vm > 0
    h3 = int(np.sum(same_sign != (s == 0)))
    pair = np.abs(vb + vm); ab, am = np.abs(vb), np.abs(vm)
    pred = np.abs(ab + ((-1.0)**s)*am)
    scale = np.maximum(ab, am)
    h4 = float(np.max(np.abs(pair - pred)/scale))
    h5 = int(np.sum(ab - am > pair + TOL*scale))
    dom = scale
    nc = pair > dom/2
    # premier indice à partir duquel la non-compensation tient sur tout le reste de l'échantillon
    bad = np.nonzero(~nc)[0]
    first_idx = 0 if len(bad) == 0 else int(bad[-1] + 1)
    first_prime = float(S[first_idx]) if first_idx < len(S) else None
    h6_ok = first_idx < len(S)
    h7 = float(np.max(np.abs(vm - vb)/ab)) if beta == 0.5 else None
    shifted_share = float(np.mean(s != 0))
    r = dict(label=label, beta=beta, T=T, delta=delta, delta_over_pi=delta/math.pi,
             H1_violations=h1, H2_violations=h2, H3_violations=h3, H4_max_rel=h4, H5_violations=h5,
             H6_holds_from_index=first_idx, H6_holds_from_prime=first_prime, H6_ok=bool(h6_ok),
             H6_violations_total=int(len(bad)), H7_line_max_rel=h7,
             shifted_word_share=shifted_share, abs_delta_over_pi=abs(delta)/math.pi,
             shift_counts={str(int(u)): int(c) for u, c in zip(*np.unique(s, return_counts=True))})
    ok = h1 == 0 and h2 == 0 and h3 == 0 and h4 <= TOL and h5 == 0 and h6_ok and (h7 is None or h7 <= 1e-15)
    r["ok"] = bool(ok)
    lg(f"{label:22s} β={beta:.2f} T={T:.6f} δ/π={delta/math.pi:+.4f} | H1 {h1} H2 {h2} H3 {h3} H4 {h4:.1e} H5 {h5} "
       f"| H6 dès idx {first_idx} (p={first_prime}) viol={len(bad)} | part décalée {shifted_share:.4f} vs |δ|/π {abs(delta)/math.pi:.4f}"
       + (f" | H7 {h7:.1e}" if h7 is not None else "") + f" | {'OK' if ok else 'ECHEC'}")
    return r

ranks = [1, 10, 100, 1000, 10000, 100000]
results = []
for r_ in ranks:
    T = float(G[r_-1])
    for beta in [0.3, 0.4, 0.45, 0.5]:
        results.append(check(beta, T, f"rang{r_}_b{beta}"))
allok = all(r["ok"] for r in results)
lg(f"TOTAL : {len(results)} couples ; tous OK : {allok}")
json.dump(dict(zeros_sha=sha, sample=len(S), seed=452, tol=TOL, results=results, all_ok=allok),
          open(os.path.join(OUT, "data", "e452a_results.json"), "w"), indent=1)

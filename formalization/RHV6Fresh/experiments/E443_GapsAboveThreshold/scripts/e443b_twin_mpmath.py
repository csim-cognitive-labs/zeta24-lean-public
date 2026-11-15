# -*- coding: utf-8 -*-
"""E443(b) — jumeau mpmath (30 chiffres) : seuils x*, x** et borne A6 sur un sous-échantillon de cellules."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e443b.log")); mp.mp.dps = 30
G, sha = load_zeros(log)
res = {"sha256": sha, "dps": 30, "towers": {}}
d64 = json.load(open(os.path.join(OUT, "data", "e443a_results.json")))["towers"]
for rank in [1, 100, 1000, 10000, 100000]:
    T = mp.mpf(repr(float(G[rank - 1]))); r = mp.exp(mp.pi / T)
    xs = mp.findroot(lambda x: x * (r - 1) - mp.log(x), mp.mpf(d64["rank%d" % rank]["xstar"]))
    xs2 = mp.findroot(lambda x: x * (1 - 1 / r) - (mp.log(x) + 2 * mp.sqrt(x * r) * mp.log(x * r)), mp.mpf(d64["rank%d" % rank]["xstar2"]))
    rel1 = float(abs(xs - d64["rank%d" % rank]["xstar"]) / xs); rel2 = float(abs(xs2 - d64["rank%d" % rank]["xstar2"]) / xs2)
    res["towers"]["rank%d" % rank] = {"xstar_mp": float(xs), "xstar2_mp": float(xs2), "xstar_relerr_vs_float64": rel1, "xstar2_relerr_vs_float64": rel2}
    log("rang %d : x* = %s (écart %.1e), x** = %s (écart %.1e)" % (rank, mp.nstr(xs, 12), rel1, mp.nstr(xs2, 12), rel2))
json.dump(res, open(os.path.join(OUT, "data", "e443b_twin.json"), "w"), indent=1); log("terminé")

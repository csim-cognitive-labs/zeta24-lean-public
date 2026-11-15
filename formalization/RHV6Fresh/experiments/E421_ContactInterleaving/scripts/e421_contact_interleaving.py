# -*- coding: utf-8 -*-
"""E421 — entrelacement des contacts sur l'axe réel. Aucune donnée arithmétique."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import load_zeros, Logger
phase = lambda b, T: np.arctan2(T, b)
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e421.log"))
G, sha = load_zeros(log)
L0 = math.log(1000.0)
def logcontacts(beta, T, la, lb):
    ph = phase(beta, T)
    kmin = math.ceil((T * la - ph) / math.pi); kmax = math.floor((T * lb - ph) / math.pi)
    k = np.arange(kmin, kmax + 1, dtype=np.float64)
    return k, (ph + k * math.pi) / T
def family(betas, Ts, la, lb):
    pos = []; lab = []; ks = []
    for i, (b, T) in enumerate(zip(betas, Ts)):
        k, lc = logcontacts(b, T, la, lb); pos.append(lc); lab.append(np.full(len(lc), i)); ks.append(k)
    pos = np.concatenate(pos); lab = np.concatenate(lab); ks = np.concatenate(ks)
    o = np.argsort(pos, kind="stable"); return pos[o], lab[o], ks[o]
def between_counts(pos, lab, i, j):
    """nombre de contacts de la Tour j entre contacts consécutifs de la Tour i (intervalles complets)."""
    idx = np.nonzero(lab == i)[0]; cnt = []
    for a, b in zip(idx[:-1], idx[1:]):
        cnt.append(int(np.sum(lab[a + 1:b] == j)))
    return np.array(cnt)
res = []
for N in [10, 100, 1000, 10000, 2001052]:
    Ts = G[:N].astype(float); betas = np.full(N, 0.5)
    L = math.pi / Ts[0] if N < 2001052 else 10 * math.pi / Ts[-1]
    pos, lab, ks = family(betas, Ts, L0, L0 + L)
    r = dict(N=N, fenetre_log=[L0, L0 + L], n_contacts=int(len(pos)))
    d = np.diff(pos); r["espacement_min"] = float(d.min()); r["espacement_median"] = float(np.median(d)); r["espacement_max"] = float(d.max())
    r["pas_moyen"] = L / len(pos); r["coincidences_1e-12"] = int(np.sum(d < 1e-12))
    r["coincidences_relatives_1e-3_pas_moyen"] = int(np.sum(d < 1e-3 * r["pas_moyen"]))
    r["espacement_min_en_pas_moyen"] = float(d.min() / r["pas_moyen"])
    # comptes entre contacts consécutifs : sous-famille dédiée sur 50 pas de la Tour basse (les fenêtres ci-dessus
    # ne contiennent qu'un pas de la Tour 1, donc aucun intervalle complet pour les paires (1, j))
    pairs = [(0, 1), (0, 2), (1, 2), (0, 99), (0, 999), (0, N - 1), (99, N - 1)]
    pr = {}
    for (i, j) in pairs:
        if i >= N or j >= N or i == j: continue
        Lp = 50 * math.pi / Ts[i]
        ppos, plab, _ = family([0.5, 0.5], [Ts[i], Ts[j]], L0, L0 + Lp)
        c = between_counts(ppos, plab, 0, 1); q = Ts[j] / Ts[i]
        ok = bool(np.all((c == math.floor(q)) | (c == math.ceil(q)))) if len(c) else None
        pr["%d-%d" % (i + 1, j + 1)] = dict(rapport_T=q, n_intervalles=int(len(c)), comptes_min=int(c.min()) if len(c) else None,
                                            comptes_max=int(c.max()) if len(c) else None, dans_plancher_plafond=ok)
    r["paires"] = pr
    # identité du décalage (vérification exacte sur 1000 couples)
    rng = np.random.default_rng(0); m = min(1000, len(pos) - 1); ii = rng.integers(0, len(pos), m); jj = rng.integers(0, len(pos), m)
    lhs = pos[jj] - pos[ii]
    rhs = (phase(0.5, Ts[lab[jj]]) + ks[jj] * math.pi) / Ts[lab[jj]] - (phase(0.5, Ts[lab[ii]]) + ks[ii] * math.pi) / Ts[lab[ii]]
    r["identite_decalage_max_err"] = float(np.max(np.abs(lhs - rhs)))
    # phase des contacts de chaque Tour dans le cycle de la Tour 1 (fraction de π)
    if N < 2001052:   # fenêtre = un cycle complet de la Tour 1 ; pour 2 001 052 la fenêtre est 10 pas de T_max : sans objet
        fr = np.mod(Ts[0] * pos - phase(0.5, Ts[0]), math.pi) / math.pi
        h, _ = np.histogram(fr[lab != 0], bins=10, range=(0, 1))
        r["histogramme_phase_dans_cycle_tour1"] = h.tolist()
    else:
        r["histogramme_phase_dans_cycle_tour1"] = None
    log("N=%d : %d contacts, pas moyen %.3e, min %.3e (%.2e pas), coïncidences abs %d rel %d, décalage %.1e, paires %s" % (N, len(pos), r["pas_moyen"], r["espacement_min"], r["espacement_min_en_pas_moyen"], r["coincidences_1e-12"], r["coincidences_relatives_1e-3_pas_moyen"], r["identite_decalage_max_err"], {k: (v["comptes_min"], v["comptes_max"], v["dans_plancher_plafond"]) for k, v in pr.items()}))
    res.append(r)
json.dump(res, open(os.path.join(OUT, "data", "e421_interleaving.json"), "w"), indent=1)
# synthétique séparé
N = 10000; Ts = G[:N].astype(float); Tstar = 0.5 * (float(G[99]) + float(G[100])); L = math.pi / Ts[0]
syn = []
pos_on, lab_on, _ = family(np.full(N + 1, 0.5), np.append(Ts, Tstar), L0, L0 + L)
rank_on = np.nonzero(lab_on == N)[0]
for b in (0.5, 0.3, 0.45, 0.49):
    betas = np.append(np.full(N, 0.5), b)
    pos, lab, _ = family(betas, np.append(Ts, Tstar), L0, L0 + L)
    rank = np.nonzero(lab == N)[0]
    shift = (phase(b, Tstar) - phase(0.5, Tstar)) / Tstar
    s = dict(beta=b, T=Tstar, n_contacts_tour=int(len(rank)), deplacement_log=shift, deplacement_en_pas=shift / (math.pi / Tstar),
             somme_changements_rang=int(np.sum(np.abs(rank - rank_on))) if len(rank) == len(rank_on) else None,
             max_changement_rang=int(np.max(np.abs(rank - rank_on))) if len(rank) == len(rank_on) else None)
    # paire miroir : distance minimale entre contacts de β et de 1−β
    _, la = logcontacts(b, Tstar, L0, L0 + L); _, lb = logcontacts(1 - b, Tstar, L0, L0 + L)
    dm = np.min(np.abs(la[:, None] - lb[None, :])) if len(la) and len(lb) else None
    s["miroir_distance_min_en_pas"] = (dm / (math.pi / Tstar)) if dm is not None else None
    s["miroir_distance_attendue_en_pas"] = abs(phase(b, Tstar) - phase(1 - b, Tstar)) / math.pi
    log("synthétique β=%.2f : déplacement %.3f pas, changements de rang Σ=%s max=%s, miroir dist. min %.4f pas (attendu %.4f)" % (b, s["deplacement_en_pas"], s["somme_changements_rang"], s["max_changement_rang"], s["miroir_distance_min_en_pas"], s["miroir_distance_attendue_en_pas"]))
    syn.append(s)
json.dump(syn, open(os.path.join(OUT, "data", "e421_synthetic.json"), "w"), indent=1)
log("terminé")

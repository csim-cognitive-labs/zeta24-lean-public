# -*- coding: utf-8 -*-
"""E423 — ON contre OFF aux contacts, déplacements et valeurs conservés. SYNTHÉTIQUE, séparé. Aucune donnée arithmétique."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import load_zeros, Logger, phase, contacts_in, CHUNK
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e423.log"))
G, sha = load_zeros(log)
A, X = 100.0, 1000.0
def val(rho, x): return np.exp(rho * np.log(x)) / rho
def sum_raw_many(xs, gam):
    lx = np.log(xs); out = np.zeros(len(xs)); B = 32
    for i in range(0, len(gam), CHUNK):
        rho = 0.5 + 1j * gam[i:i + CHUNK]
        for j in range(0, len(xs), B):
            out[j:j + B] += (2.0 * np.real(np.exp(np.outer(lx[j:j + B], rho)) / rho)).sum(axis=1)
    return out
def axis_passages(rhos, la, lb, step):
    """racines de Im Σ x^ρ/ρ (en log x) sur [la, lb], grille 64 points par pas + bissection."""
    grid = np.linspace(la, lb, int((lb - la) / step * 64) + 2)
    f = lambda l: sum(np.imag(np.exp(r * l) / r) for r in rhos)
    v = f(grid); roots = []
    for i in np.nonzero(np.sign(v[1:]) != np.sign(v[:-1]))[0]:
        a, b = grid[i], grid[i + 1]; fa = v[i]
        for _ in range(60):
            m = 0.5 * (a + b); fm = f(m)
            if np.sign(fm) == np.sign(fa): a, fa = m, fm
            else: b = m
        roots.append(0.5 * (a + b))
    return np.array(roots)
res = []
for (r1, r2) in [(1, 2), (100, 101), (2000, 2001)]:
    T = 0.5 * (float(G[r1 - 1]) + float(G[r2 - 1])); step = math.pi / T
    kon, Con = contacts_in(0.5, T, A, X); rho_on = 0.5 + 1j * T; von = val(rho_on, Con).real
    S_on = sum_raw_many(Con[:15], G)      # famille réelle de ligne aux contacts ON de T*
    for b in (0.3, 0.45, 0.49):
        rho_b = b + 1j * T; rho_m = (1 - b) + 1j * T
        kb, Cb = contacts_in(b, T, A, X); vb = val(rho_b, Cb)
        # aligner sur k commun
        kc = np.intersect1d(kon, kb); ion = np.searchsorted(kon, kc); ib = np.searchsorted(kb, kc)
        shift = np.log(Cb[ib]) - np.log(Con[ion])
        r = dict(T=T, milieu=[r1, r2], beta=b, pas_log=step, n_contacts_communs=int(len(kc)),
                 deplacement_log_mesure=float(shift[0]), deplacement_log_predit=(phase(b, T) - phase(0.5, T)) / T,
                 deplacement_constance_max=float(np.max(np.abs(shift - shift[0]))), deplacement_en_pas=float(shift[0] / step))
        r["accord_signe_meme_k"] = float(np.mean(np.sign(vb[ib].real) == np.sign(von[ion])))
        r["max_im_rel_off_a_ses_contacts"] = float(np.max(np.abs(vb[ib].imag) / np.abs(vb[ib])))
        ratio = np.abs(vb[ib]) / np.abs(von[ion]); pred = Cb[ib] ** b * abs(rho_on) / (Con[ion] ** 0.5 * abs(rho_b))
        r["rapport_modules_min"] = float(ratio.min()); r["rapport_modules_max"] = float(ratio.max())
        r["rapport_modules_err_pred_max"] = float(np.max(np.abs(ratio - pred) / pred))
        # paire miroir
        km, Cm = contacts_in(1 - b, T, A, X)
        dmin = np.min(np.abs(np.log(Cb)[:, None] - np.log(Cm)[None, :]))
        r["miroir_distance_min_en_pas"] = float(dmin / step); r["miroir_distance_predite_en_pas"] = abs(phase(b, T) - phase(1 - b, T)) / math.pi
        vm_at_b = val(rho_m, Cb); r["miroir_im_rel_aux_contacts_de_beta_median"] = float(np.median(np.abs(vm_at_b.imag) / np.abs(vm_at_b)))
        roots = axis_passages([rho_b, rho_m], math.log(A), math.log(X), step)
        # déplacement des passages de la paire par rapport aux contacts ON : plus proche contact ON
        lon = np.log(Con); dd = np.array([roots[i] - lon[np.argmin(np.abs(lon - roots[i]))] for i in range(len(roots))])
        r["paire_passages_axe_n"] = int(len(roots)); r["paire_passages_n_on"] = int(len(Con))
        r["paire_passages_deplacement_en_pas_median"] = float(np.median(dd) / step) if len(dd) else None
        r["paire_passages_deplacement_en_pas_max"] = float(np.max(np.abs(dd)) / step) if len(dd) else None
        # valeurs réelles de la paire à ses propres passages
        if len(roots):
            vp = sum(np.exp(rr * roots) / rr for rr in [rho_b, rho_m]); vp_on = val(rho_on, np.exp(roots))
            r["paire_valeur_axe_rms"] = float(np.sqrt(np.mean(vp.real ** 2))); r["on_valeur_memes_positions_rms"] = float(np.sqrt(np.mean(vp_on.real ** 2)))
            r["paire_valeur_axe_im_max"] = float(np.max(np.abs(vp.imag)))
        # contexte collectif aux 15 contacts ON : insertion
        ins_off = 2 * val(rho_b, Con[:15]).real; ins_pair = ins_off + 2 * val(rho_m, Con[:15]).real; ins_on = 2 * von[:15]
        r["S_ligne_rms_15"] = float(np.sqrt(np.mean(S_on ** 2)))
        r["insertion_on_rms"] = float(np.sqrt(np.mean(ins_on ** 2))); r["insertion_off_rms"] = float(np.sqrt(np.mean(ins_off ** 2)))
        r["insertion_paire_rms"] = float(np.sqrt(np.mean(ins_pair ** 2)))
        r["part_insertion_paire_sur_S_mediane"] = float(np.median(np.abs(ins_pair) / np.abs(S_on)))
        Sb = sum_raw_many(Cb[ib][:15], G); r["S_ligne_aux_contacts_deplaces_rms_15"] = float(np.sqrt(np.mean(Sb ** 2)))
        r["S_ligne_variation_on_vs_deplaces_rms"] = float(np.sqrt(np.mean((Sb - S_on[ion[:15]]) ** 2))) if len(ion) >= 15 else None
        # jumeau mpmath
        mp.mp.dps = 25; e = []
        for x in Cb[:3]:
            vv = mp.exp(mp.mpc(b, T) * mp.log(mp.mpf(float(x)))) / mp.mpc(b, T); e.append(float(abs(vv.real - val(rho_b, x).real) / abs(vv)))
        r["jumeau_mpmath_max_err_rel"] = max(e)
        log("T*=%.4f β=%.2f : dépl. %.4f pas (const %.1e), signe %.2f, rapport modules [%.3f, %.3f], miroir dist %.4f pas (préd %.4f), passages paire %d/%d dépl. méd. %s pas, insertion paire/S %.3e" % (
            T, b, r["deplacement_en_pas"], r["deplacement_constance_max"], r["accord_signe_meme_k"], r["rapport_modules_min"], r["rapport_modules_max"], r["miroir_distance_min_en_pas"], r["miroir_distance_predite_en_pas"], r["paire_passages_axe_n"], r["paire_passages_n_on"], r["paire_passages_deplacement_en_pas_median"], r["part_insertion_paire_sur_S_mediane"]))
        res.append(r)
json.dump(res, open(os.path.join(OUT, "data", "e423_synthetic.json"), "w"), indent=1)
log("terminé")

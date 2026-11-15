# -*- coding: utf-8 -*-
"""E416 — écarts premiers reconstruits SANS les premiers : classification pré-enregistrée (valeur
admissible la plus proche parmi {0, log n, log n / k pour n = m^k}) appliquée aux poids spectraux
Λ̂_H(n) d'E415 (canaux A et B), puis suite des événements premiers reconstruits et de leurs écarts.
La suite réelle n'est consultée qu'APRÈS la reconstruction (validation)."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import *
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
E415 = os.path.join(OUT, "..", "E415_RawEventReconstruction", "data")
log = Logger(os.path.join(OUT, "logs", "e416.log"))
TRUNC = [3, 10, 40, 100, 300, 1000, 5000, 10000, 100000, 1000000, 2001052]
WINDOWS = {"W1": list(range(3, 301)), "W2": list(range(10000, 10061)), "W3": list(range(100000, 100031))}
results = {}
for wname, W in WINDOWS.items():
    lamA = np.load(os.path.join(E415, "lamA_%s.npy" % wname)); lamB = np.load(os.path.join(E415, "lamB_%s.npy" % wname))
    results[wname] = {}
    for chan, L in (("A", lamA), ("B", lamB)):
        for j, H in enumerate(TRUNC):
            # --- reconstruction (aucune donnée arithmétique) ---
            labels = [classify(n, L[i, j])[1] for i, n in enumerate(W)]
            rec_primes = [n for n, l in zip(W, labels) if l == "prime"]
            rec_events = [n for n, l in zip(W, labels) if l != "none"]
            rec_gaps = [q - p for p, q in zip(rec_primes, rec_primes[1:])]
            # --- VALIDATION (après) ---
            lam, isp = sieve_lambda(W[-1] + 2)
            true_primes = [n for n in W if isp[n]]
            true_events = [n for n in W if lam[n] > 0]
            true_gaps = [q - p for p, q in zip(true_primes, true_primes[1:])]
            sp, se = set(rec_primes), set(rec_events); tp, te = set(true_primes), set(true_events)
            first_div = next((k for k, (a, b) in enumerate(zip(rec_gaps, true_gaps)) if a != b), None)
            if first_div is None and len(rec_gaps) != len(true_gaps): first_div = min(len(rec_gaps), len(true_gaps))
            exact_gaps = sum(1 for a, b in zip(rec_gaps, true_gaps) if a == b) if first_div is None else first_div
            abs_err = sum(abs(a - b) for a, b in zip(rec_gaps, true_gaps))
            r = dict(zeros=H, events_ok=len(se & te), events_false=len(se - te), events_missed=len(te - se),
                     primes_ok=len(sp & tp), primes_false=len(sp - tp), primes_missed=len(tp - sp),
                     gaps_total=len(true_gaps), gaps_exact_prefix=exact_gaps, first_divergence_index=first_div,
                     first_divergence_prime=(rec_primes[first_div] if first_div is not None and first_div < len(rec_primes) else None),
                     gap_abs_error_sum=abs_err, all_gaps_exact=(first_div is None))
            results[wname]["%s_%d" % (chan, H)] = r
            log("%s canal %s zéros=%8d : événements ok/faux/manqués %3d/%3d/%3d | premiers ok/faux/manqués %3d/%3d/%3d | écarts exacts (préfixe) %3d/%3d | 1re divergence %s | Σ|Δg| %d"
                % (wname, chan, H, r["events_ok"], r["events_false"], r["events_missed"], r["primes_ok"], r["primes_false"], r["primes_missed"],
                   exact_gaps, len(true_gaps), str(first_div), abs_err))
            if H == 2001052:
                with open(os.path.join(OUT, "data", "e416_%s_%s_sequences.txt" % (wname, chan)), "w") as f:
                    f.write("# premiers reconstruits (canal %s, %d zéros) :\n%s\n# écarts reconstruits :\n%s\n# premiers réels (validation) :\n%s\n# écarts réels :\n%s\n"
                            % (chan, H, rec_primes, rec_gaps, true_primes, true_gaps))
json.dump(results, open(os.path.join(OUT, "data", "e416_results.json"), "w"), indent=1)
log("terminé")

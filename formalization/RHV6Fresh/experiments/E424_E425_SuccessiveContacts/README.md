# E424–E425 — Constraints between successive Towers read at the contacts (pre-registered 2026-11-03)

> Français : [README.fr.md](README.fr.md)

Author's directive ("strategy of real contacts", §19.39): exploit the contacts of the Towers with the real axis to
recover height and real part, amplitude ratios, relative phases between Towers, mirror contacts, constraints
between successive Towers and the junction to prime events. No spectral projection, no detection
by thresholds, no integrated primitives, no unit cells as a support for reconstruction, no logarithmic
integral. Reference Lean module: `Terminal/SuccessiveContactConstraints.lean` (isolated, compiled before execution).

## E424 — Cross reading between successive Towers at the successor's contacts
For each pair of consecutive zeros (e, l) = (rank n, rank n+1) over the 2,001,052 Odlyzko heights (placed on the
line), at the first two contacts of l in [2, ∞):
* cross ratio of e at the contacts of l: |e(C_{k+1}(l))|/|e(C_k(l))|; own ratio of l;
* reading of the difference of radial positions: (T_l/π)·log(ratio_e/ratio_l) — **compiled prediction
  (`radial_difference_of_crossRatios`): 0 for ON→ON, ½ − β_l for a synthetic OFF successor**;
* reading of the radial position of the predecessor: (T_l/π)·log(ratio_e) — prediction ½;
* relative phase step of e between two contacts of l: arg(e(C_{k+1})/e(C_k)) = T_e·π/T_l modulo 2π
  (`towerValue_step_at_contacts`); since T_e < T_l < 2T_l, the height of the predecessor is read without ambiguity:
  T̂_e = (T_l/π)·(step modulo 2π). Maximal error recorded; it is expected to grow like T·ε (conditioning).
Separate synthetic: real ON predecessor (ranks 1, 100, 2,000, 100,000), synthetic successor at the midpoint height of
zeros (n+1, n+2) — never the height of a real zero — with β_l ∈ {0.3, 0.45, 0.49}; reading ½ − β_l expected; mirror
pair (β_l, 1−β_l): reading 2β_l − 1 expected.
Deterministic twin: mpmath 30 digits on 6 real pairs and all synthetic pairs.
Criterion: radial readings to within 10⁻⁹; T̂_e to within T_l·10⁻⁹; otherwise recorded as is.

## E425 — Mirror pair at the member's contacts and position of the prime of the same rank
(a) At the contacts of a synthetic OFF member (β ∈ {0.3, 0.45, 0.49}, midpoint heights of zeros (1,2), (100,101),
(2000,2001), (100000,100001)), imaginary part of the sum of the pair (member + mirror) normalized by the modulus of the
mirror: **compiled prediction (`mirror_im_at_contact`): (−1)^k · sin(relative phase), relative phase =
arctan(T/β) − arctan(T/(1−β)), never zero (`pair_axis_at_contact_iff`)**. ON control at real heights (β = ½):
imaginary part zero up to rounding. mpmath twin on 5 contacts per Tower.
(b) Junction: to the zero of rank m (1-indexed) is associated the m-th prime p_m (`occurrence`, corpus: 0-indexed rank n
↦ `Nat.nth Nat.Prime n`). Stage position s = (T·log p_m − arctan(T/β))/π, contact index k = ⌊s⌋, fraction f = s − k,
sign of the real value at the enclosing contact (−1)^k, cosine of the phase at p_m (cos πs). Over the 2,001,052 zeros:
deterministic histogram of f (20 classes), proportion of even k, mean of cos πs. Displacement twin (as E423):
same heights with β = 0.3; **compiled prediction (`arrival_cell_same_or_previous`): k(0.3) ∈ {k(½) − 1, k(½)} in
100%**; frequency of the notch recorded. No prediction is pre-registered on the shape of the histogram of f: it is
measured, not read as a law. mpmath twin on 10 ranks.

Nothing here presumes that these readings exclude OFF zeros; an exclusion would be admitted only if compiled.

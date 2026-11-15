# E417 — Limit and high frequencies (pre-registered on 2026-11-03)

> Français : [README.fr.md](README.fr.md)

**Question.** How do the high frequencies form the breaks? Convergence off and at the events, width of the finite
transitions, Gibbs overshoot, raw channel against integrated channel, maximal height, necessary precision.

**Measures.** (1) raw profile ψ̂₀_H(p + t), t ∈ [−½, ½], p ∈ {101, 1009, 10007}, H ∈ {10³, 10⁴, 10⁵, 10⁶, γ_max}: 10–90% width
of the jump, overshoot, rms outside three scales, against the scale πp/T_max (checked, not assumed);
(2) from E415 (W1): rms of E_H at the events and off the events, channels A and B, and products B·T_max, A·√T_max;
(3) smallest truncation making all gaps of W1 exact (E416), by channel.

**Results.** `RESULTS.md`, `data/e417_results.json`, `data/profile_p*_H*.npy`, `logs/e417.log`.

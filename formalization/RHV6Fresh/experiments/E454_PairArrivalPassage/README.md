# E454 — K4: the pair read as a passage from the low arrival — pre-registration

> Français : [README.fr.md](README.fr.md)

Date: 2026-11-08. Status: pre-registered before any compilation (§19.77). Green light from the author after K3
("continue, you have the green light"). Orders: total spectral ban (use and citation; two terms at most, no sum of
Towers); third order (contacts read `β`); R-E446; §19.44; forbidden "amplitude against budget"; no premise equivalent
to RH; useful range `β ≤ 1/2` for the arrival (§19.76); at most two compilation attempts, each logged in `attempts/`.

## Question K4 (§19.77.2)
K0–K3 describe the pair by its two terms. What does the corpus compile on the pair read as a PASSAGE of the canonical
enumeration: place of the two members, passage leaving the low arrival, frequency reading of the two members, relation
to the single premise?

## Check of non-equivalence with RH (done before, §19.77.3)
No hypothesis posed; conditions = cases on a given passage or zero; L6 = contrapositive of an already compiled
equivalence; nothing is asserted about the existence of low arrivals. Expected answer recorded in advance: form of the
OFF passage, NO contradiction; the frontier remains the single premise (⟺ RH).

## Lean statements (isolated module `Terminal/PairArrivalPassage.lean`, import `PairWordInversion`)
L1 `arrival_low_of_off`; L2 `passage_height_le`, `passage_frozen_of_low_entry`, `passage_right_of_low_entry`;
L3 `low_arrival_precedes_mirror`, `low_entry_successor_radial_le`, `low_entry_successor_band`;
L4 `low_arrival_contact_ratio_lt`, `low_arrival_term_ratio_tendsto_zero`; L5 `frozen_passage_same_word_slope`;
L6 `low_entry_not_expected`, `frozen_passage_has_low_member`; L7 `arrival_exit_dichotomy`.

## Experiments
None: K4 produces no numerical conclusion. Execution evidence = compilation logs in `attempts/`.

## Criterion
Verdict A if the thirteen statements compile in at most two attempts, standard axioms, zero warnings in the module,
empty grep of the ban, full `lake build RHV6Fresh` green. Otherwise verdict B with each failure recorded. In all cases
the answer is recorded as is; any contradiction that appeared would be checked for non-equivalence before being stated.

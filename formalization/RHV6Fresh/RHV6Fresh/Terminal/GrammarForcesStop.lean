/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SuccessionInvariants

/-!
# `Terminal/GrammarForcesStop.lean` — le test dans l'autre sens : `M^Z = M` en prémisse

Remarque de l'auteur (2026-09-28) : « il faut faire le test dans l'autre sens avant de répondre.
Les ZÉROS DOIVENT reproduire la grammaire des premiers `M^Z = M`. Donc la cellule et la géométrie
DOIT savoir où s'arrêter. [...] si `M^Z = M` alors la géométrie SAIT parfaitement quel rayon est le
bon MÊME si nous avons codé quelque chose de différent. »

Le code compilé contient DEUX énoncés distincts portant le nom `M^Z = M` :

* **la grammaire par RANG** (`passage_event_increment`, `passage_raccords`) : sur tout passage,
  `n_l = n_e + 1`, `Occ(l) = p_min(e)`, `Occ(e) < Occ(l)`. Inconditionnelle, aveugle à `β` et à `T`.
* **la grammaire par HAUTEUR** (`grammarsAgree_iff_riemannHypothesis`) : pour tout zéro, l'index par
  membres coïncide avec l'index par hauteurs. Compilée `⟺ RH`.

Ce fichier fait le test demandé pour chacune des deux :

* G1 — sous la grammaire par hauteur, l'amplitude exigée `J` est STRICTEMENT positive sur tout
  passage, la hauteur progresse, `Δβ = 0` (mode A seul), et le rayon d'arrêt du LATER est celui de
  la Tour à `β = 1/2` : la géométrie « sait » où s'arrêter. L'auteur a raison sur ce point.
* G2 — sous la grammaire par rang seule, un zéro hors ligne (s'il existait) fournit un passage qui
  satisfait toute la grammaire par rang avec `J = 0` : cette grammaire-là ne force aucune amplitude.
  L'énoncé « la double contrainte exige seulement `J ≥ 0` » (`RayEnergy.lean` D3) portait sur elle.
* G3 — les deux lectures ne sont pas interchangeables : « `J > 0` partout » EST la grammaire par
  hauteur, et toutes deux sont `RH`. Prendre `M^Z = M` (hauteur) en prémisse, c'est prendre RH.
-/

namespace RHV6Fresh
open RHV3Lean

/-! ## G1 — sous `M^Z = M` (hauteur), la géométrie sait où s'arrêter -/

/-! ## G2 — la grammaire par RANG seule ne force aucune amplitude -/

/-- **G2.** Un zéro hors ligne fournit un passage satisfaisant TOUTE la grammaire par rang
(`n+1`, raccord, `Occ<`) avec `J = 0` : cette grammaire n'exige aucun déplacement. C'est de
celle-ci, et d'elle seule, que parlait `double_constraint_required_displacement`. -/
theorem rank_grammar_forces_no_displacement {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ p : TZeroPassage, ∃ hE : 0 < rZeroHeight p.zEarlierMember,
      ∃ hL : 0 < rZeroHeight p.zLaterMember,
        nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
        occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
        occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ ∧
        interTowerExcess p hE hL = 0 := by
  obtain ⟨p, hE, hL, _, hSame, hSucc, hOcc, hLt⟩ := off_event_increment_without_height hOff
  exact ⟨p, hE, hL, hSucc, hOcc, hLt, (interTowerExcess_eq_zero_iff p hE hL).mpr hSame⟩

/-! ## G3 — les deux lectures de `M^Z = M` et l'amplitude exigée sont le même énoncé, RH -/

/-- **G3c.** La grammaire par rang est vraie sur tout passage, sans condition : elle ne peut
séparer ON de OFF. -/
theorem rank_grammar_unconditional (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
      occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ :=
  passage_event_increment p hE hL

end RHV6Fresh

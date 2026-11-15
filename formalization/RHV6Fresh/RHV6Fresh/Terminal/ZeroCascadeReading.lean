/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GrammarTransportLaw
import RHV6Fresh.Terminal.EngagedProgression
import RHV6Fresh.Grammar.ExpectedMinimum

/-!
# Le zéro suivant lit le zéro précédent : cascade de la fréquence (auteur, 2026-10-19, dix-huitième message)

Position de l'auteur, mot pour mot : « les zéros sont liés entre eux ; ils forment un ensemble stable ; cette stabilité impose
que chaque zéro plus haut possède une fréquence supérieure au zéro précédent, et cascade ce besoin sur le zéro suivant :
nouvelle hauteur, nouvelle fréquence, afin de reproduire exactement, mais à l'infini, les écarts des premiers » ; « pour
transmettre la fréquence il faut forcément que le zéro suivant lise le zéro précédent : c'est la preuve que les zéros sont
liés ».

Théorème compilé (`next_zero_reads_previous`, axiomes standard, toute position radiale des deux zéros) : sur tout passage
`e → l`, le zéro suivant
* est déterminé par le précédent (un seul successeur par zéro) ;
* porte le rang suivant ;
* a pour occurrence le premier minimum attendu du précédent (il lit le premier du précédent) ;
* LIT LA FRÉQUENCE DU PRÉCÉDENT : d'une rencontre propre à la suivante, l'accroissement du déplacement de ses rencontres
  par rapport à celles du précédent vaut exactement la différence des deux pas `π/T_l − π/T_e` ; la part radiale s'y
  annule ; la hauteur du précédent est donc retrouvée depuis le seul zéro suivant et cet accroissement
  (`previous_frequency_read_by_next`).
Portée : cette lecture vaut pour toute position radiale ; elle établit le lien, elle ne fixe pas la position radiale du
suivant. La cascade par la seule fréquence (`NoRadialShift`) reste l'unique condition ouverte de la chaîne.
-/

namespace RHV6Fresh

open RHV3Lean

/-- Accroissement, d'une rencontre propre à la suivante, du déplacement des rencontres de `l` par rapport à celles de `e`. -/
noncomputable def cascadeIncrement (e l : TrueZero) (k : ℤ) : ℝ :=
  Real.log (contactMinusAt l (k + 1) / contactMinusAt e (k + 1)) -
    Real.log (contactMinusAt l k / contactMinusAt e k)

/-- **Le zéro suivant lit la fréquence du précédent** : l'accroissement vaut la différence des pas, toute position
radiale (la part radiale s'annule). -/
theorem cascadeIncrement_eq (e l : TrueZero) (k : ℤ) :
    cascadeIncrement e l k = Real.pi / rZeroHeight l.1 - Real.pi / rZeroHeight e.1 := by
  unfold cascadeIncrement
  rw [contact_log_ratio, contact_log_ratio, lineHeightShift_split, lineHeightShift_split]
  push_cast
  ring

/-- **La hauteur du précédent est retrouvée depuis le seul zéro suivant et l'accroissement de ses rencontres.** -/
theorem previous_frequency_read_by_next (e l : TrueZero) (k : ℤ) :
    rZeroHeight e.1 = Real.pi / (Real.pi / rZeroHeight l.1 - cascadeIncrement e l k) := by
  rw [cascadeIncrement_eq, sub_sub_cancel]
  have he : rZeroHeight e.1 ≠ 0 := e.2.ne'
  field_simp

/-- **Hausse de fréquence lue** : sur un passage qui monte, l'accroissement est strictement négatif (les rencontres du
suivant se resserrent par rapport à celles du précédent), toute position radiale. -/
theorem cascadeIncrement_neg (e l : TrueZero) (hT : rZeroHeight e.1 < rZeroHeight l.1) (k : ℤ) :
    cascadeIncrement e l k < 0 := by
  rw [cascadeIncrement_eq]
  have : Real.pi / rZeroHeight l.1 < Real.pi / rZeroHeight e.1 := div_lt_div_of_pos_left Real.pi_pos e.2 hT
  linarith

/-- **Le zéro suivant lit le zéro précédent (les zéros sont liés)** : sur tout passage, le suivant est déterminé par le
précédent, porte le rang suivant, a pour occurrence le premier minimum attendu du précédent et lit sa fréquence à toute
rencontre propre. Axiomes standard ; toute position radiale. -/
theorem next_zero_reads_previous (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    (∀ p' : TZeroPassage, p'.zEarlierMember = p.zEarlierMember → p'.zLaterMember = p.zLaterMember) ∧
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
    occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
    (∀ k : ℤ, rZeroHeight p.zEarlierMember =
      Real.pi / (Real.pi / rZeroHeight p.zLaterMember -
        cascadeIncrement ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k)) :=
  ⟨fun _ h => passage_successor_unique h,
   eventIndex_succ_of_passage p hE,
   (expectedMinimumPrime_eq_laterOccurrence p hE hL).symm,
   fun k => previous_frequency_read_by_next ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k⟩

/-- **La lecture est aveugle à la position radiale** : la cascade par la seule fréquence (aucune part radiale) n'en découle
pas ; sous un départ ON elle reste ⟺ `β_l = 1/2` (`noRadialShift_iff_onLine`). -/
theorem cascade_reading_radial_blind (e l l' : TrueZero) (hT : rZeroHeight l.1 = rZeroHeight l'.1) (k : ℤ) :
    cascadeIncrement e l k = cascadeIncrement e l' k := by
  rw [cascadeIncrement_eq, cascadeIncrement_eq, hT]

#print axioms cascadeIncrement_eq
#print axioms previous_frequency_read_by_next
#print axioms next_zero_reads_previous
#print axioms cascade_reading_radial_blind

/-! ## §2 Stabilité de la cascade : le déplacement radial est le même à toutes les rencontres (auteur, 2026-10-19,
dix-neuvième message)

Position de l'auteur : « une annulation du miroir nécessaire dès le premier zéro engage un mode nécessairement stable ; les
zéros progressent par la hauteur, leur fréquence augmente ; le zéro suivant lit la hauteur du précédent et se place à la
hauteur exacte qui fait que ses contacts sont entrelacés et sa fréquence augmentée suffisamment pour atteindre EXACTEMENT les
points de rencontre ».

Compilé (axiomes standard, toute position radiale) : le déplacement des rencontres du suivant par rapport au précédent se
découpe en part de hauteur (`lineHeightShift`) et part radiale (`radialShiftAt`) ; la part radiale est LA MÊME à toutes les
rencontres (`radialShiftAt_const`) : la cascade la transporte sans la modifier. Donc atteindre exactement UNE rencontre
suffit pour les atteindre toutes (`noRadialShift_all_of_one`), et s'approcher arbitrairement près des rencontres suffit pour
les atteindre exactement (`noRadialShift_of_approach`). Sous un départ ON, rencontre exacte ⟹ contacts du suivant
entrelacés en deçà de ceux du précédent à tout indice `k ≥ 1` par la seule hausse de fréquence
(`exact_meetings_interlaced`). Portée : ces énoncés réduisent la forme de la condition (une rencontre, ou une approche) ;
ils ne fixent pas la position radiale ; sous un départ ON, la condition réduite reste ⟺ `β_l = 1/2`.
-/

/-- Part radiale du déplacement de la rencontre `k` du suivant par rapport au précédent. -/
noncomputable def radialShiftAt (e l : TrueZero) (k : ℤ) : ℝ :=
  Real.log (contactMinusAt l k / contactMinusAt e k) - lineHeightShift (rZeroHeight e.1) (rZeroHeight l.1) k

/-- La part radiale ne dépend que des deux facteurs radiaux (toute position radiale). -/
theorem radialShiftAt_eq (e l : TrueZero) (k : ℤ) :
    radialShiftAt e l k = Real.log (radialFactor l) - Real.log (radialFactor e) := by
  unfold radialShiftAt; rw [contact_log_ratio]; ring

/-- **Stabilité de la cascade** : la part radiale est la même à toutes les rencontres. -/
theorem radialShiftAt_const (e l : TrueZero) (k k' : ℤ) : radialShiftAt e l k = radialShiftAt e l k' := by
  rw [radialShiftAt_eq, radialShiftAt_eq]

theorem noRadialShift_iff_radialShiftAt (e l : TrueZero) (k : ℤ) :
    NoRadialShift e l k ↔ radialShiftAt e l k = 0 := by
  unfold NoRadialShift radialShiftAt; constructor <;> intro h <;> linarith

/-- **Une rencontre exacte suffit** : la cascade transporte l'exactitude à toutes les rencontres. -/
theorem noRadialShift_all_of_one (e l : TrueZero) {k : ℤ} (h : NoRadialShift e l k) (k' : ℤ) :
    NoRadialShift e l k' := by
  rw [noRadialShift_iff_radialShiftAt] at h ⊢
  rw [radialShiftAt_const e l k' k]; exact h

/-- **S'approcher arbitrairement près d'une rencontre suffit** : la part radiale, constante, est alors nulle à toutes. -/
theorem noRadialShift_of_approach (e l : TrueZero)
    (h : ∀ ε : ℝ, 0 < ε → ∃ k : ℤ, |radialShiftAt e l k| < ε) (k' : ℤ) : NoRadialShift e l k' := by
  rw [noRadialShift_iff_radialShiftAt]
  by_contra hne
  obtain ⟨k, hk⟩ := h _ (abs_pos.mpr hne)
  rw [radialShiftAt_const e l k k'] at hk
  exact lt_irrefl _ hk

/-- **Rencontres exactes ⟹ contacts entrelacés par la seule hausse de fréquence** : sous un départ ON et un passage qui
monte, si le suivant atteint exactement une rencontre, alors à tout indice `k ≥ 1` son contact est strictement en deçà de
celui du précédent, d'un déplacement égal à la part de hauteur seule. -/
theorem exact_meetings_interlaced (e l : TrueZero) (hT : rZeroHeight e.1 < rZeroHeight l.1) {k₀ : ℤ}
    (h : NoRadialShift e l k₀) {k : ℤ} (hk : 1 ≤ k) :
    Real.log (contactMinusAt l k / contactMinusAt e k) = lineHeightShift (rZeroHeight e.1) (rZeroHeight l.1) k ∧
    contactMinusAt l k < contactMinusAt e k := by
  have hk' := noRadialShift_all_of_one e l h k
  refine ⟨hk', ?_⟩
  have hneg : lineHeightShift (rZeroHeight e.1) (rZeroHeight l.1) k < 0 :=
    lineHeightShift_neg_of_one_le e.2 hT hk
  unfold NoRadialShift at hk'
  have hpos : 0 < contactMinusAt l k / contactMinusAt e k :=
    div_pos (contactMinusAt_positive l k) (contactMinusAt_positive e k)
  have hlt : contactMinusAt l k / contactMinusAt e k < 1 := by
    rw [← Real.log_neg_iff hpos]; linarith
  rwa [div_lt_one (contactMinusAt_positive e k)] at hlt

/-- Sous un départ ON, la condition réduite (approche des rencontres) reste ⟺ `β_l = 1/2` : certificat. -/
theorem approach_iff_onLine (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2) :
    (∀ ε : ℝ, 0 < ε → ∃ k : ℤ, |radialShiftAt e l k| < ε) ↔ rZeroRadialPosition l.1 = 1 / 2 := by
  constructor
  · intro h; exact (noRadialShift_iff_onLine e l he 0).mp (noRadialShift_of_approach e l h 0)
  · intro hl ε hε
    refine ⟨0, ?_⟩
    rw [(noRadialShift_iff_radialShiftAt e l 0).mp (noRadialShift_of_onLine e l he hl 0), abs_zero]; exact hε

#print axioms radialShiftAt_const
#print axioms noRadialShift_all_of_one
#print axioms noRadialShift_of_approach
#print axioms exact_meetings_interlaced
#print axioms approach_iff_onLine

end RHV6Fresh

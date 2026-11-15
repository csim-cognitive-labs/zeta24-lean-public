/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PrimeCapsContactsBridge

/-!
# Sonde hors build (directive R11, 2026-11-01) : le but exact laissé par la composition

Fichier VOLONTAIREMENT non compilant, hors de toute cible `lake build` ; exécuté par `lake env lean`, sortie brute dans
`ProbePrimeCapsContactsBridge.out.txt`. Le contexte contient, sous leurs noms compilés : la détermination universelle
(`F = ζ` hors du pôle, source égale, foule lue dans `F`, coordonnées du membre OFF zéro de `F`, comptage = ordres de `F`),
les deux CAP composés aux contacts, le cap de taille de foule, l'indiscernabilité de la paire par CAP et pas, le double
comptage de la paire, la décomposition exacte foule + queue, le terme OFF isolé, la borne de queue (exposant 1), le
miroir dans la même foule, le décalage des contacts, la lecture tangentielle, F8, et la rigidité de foule ⟺ RH.
Le `done` final laisse `⊢ False` non résolu : c'est le but manquant, affiché par le compilateur.
-/

open RHV3Lean RHV6Fresh RHV6Fresh.RhGap

theorem probe_prime_caps_contacts (F : ℂ → ℂ) (hF : IsPrimeDeterminedZetaContinuation F)
    (C : OffCarrier) (I : PrimeGapInterval) (hI : zeroPoint C.zero ∈ crowd I) : False := by
  -- détermination universelle, raccordée
  have hEq := primes_determine_zeta_meromorphic_continuation F hF
  have hSrc := primeDeterminedZeroSource_eq_canonical F hF
  have hUnique := primeDetermined_unique hF riemannZeta_isPrimeDetermined
  have hCrowd := primeDetermined_crowd hF I
  have hCoord := primeDetermined_coordinates hF C.n
  have hCount := primeDetermined_upperCount hF I.threshold
  have hLowIff := primeDetermined_lowZero_iff_offCarrier hF
  -- CAP × contacts, CAP × foules
  obtain ⟨A₀, hA0, hCap⟩ := crowd_card_cap
  have hCapI := hCap I
  obtain ⟨A₁, hA1, hLowCap⟩ := lower_cap_contact_interval
  obtain ⟨Cc, T₀, A₂, hA2, hUpCap⟩ := upper_cap_contact_interval
  obtain ⟨A₃, hA3, hTrans⟩ := crowd_transition_cap
  obtain ⟨A₄, hA4, hTailCap⟩ := tail_unit_window_cap
  have hBlind := C.pair_blind_to_caps_and_steps
  have hTwice := C.pair_counted_twice ((mem_crowd_iff_height_le I C.zero).mp hI)
  have hFamily := crowd_family_contacts_le I
  -- contacts et demande (R9)
  have hDecomp := crowd_tail_decomposition I
  have hSplit := C.crowdSum_split_zero I hI
  have hTail := collective_residual_bound I
  have hMirror := (C.mirror_mem_crowd_iff I).mpr hI
  have hShift := C.pair_contacts_shifted 0
  have hTan := contact_tangent_reads_radial C.zero 0
  have hTwo := coordinates_from_two_contacts C.zero 0
  have hAmp := C.mirror_density_dominates I.one_lt_upper
  have hCross := contactsCrossed_le_one_of_mem_crowd C.zero I hI
  have hF8 := crowd_alone_never_accomplishes_demand I.rank
  have hRig := crowdRadialRigidity_iff_riemannHypothesis
  have hAll := every_zero_in_some_crowd C.zero
  have hLow := C.zero_low
  done

/-- Contrôle : le même contexte se ferme dès qu'on dispose de « le zéro OFF est en ligne » — c'est-à-dire de RH au
point même ; le but manquant n'est donc ni un lemme technique ni un défaut d'import. -/
theorem control_goal_closes (C : OffCarrier) (hMissing : rZeroRadialPosition C.zero.1 = 1 / 2) : False := by
  have hLow := C.zero_low
  linarith

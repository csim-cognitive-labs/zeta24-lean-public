/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CollectiveContactRigidity

/-!
# Sonde HORS build — but terminal de la mission R9 (2026-11-01)

Non importée par `RHV6Fresh.lean`, non couverte par le glob du lakefile. Se compile seule :
`lake env lean experiments/E402_CollectiveContacts/ProbeCollectiveContactRigidity.lean` ; sortie brute dans
`ProbeCollectiveContactRigidity.out.txt`. Le but laissé ouvert est VOLONTAIRE (`done` sur un but non fermé) : c'est le
diagnostic demandé au compilateur, pas un énoncé validé. Aucun `sorry`, aucun axiome.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Question terminale R9** : la succession exacte des écarts et la reconstruction collective par les contacts
imposent-elles une rigidité radiale incompatible avec un zéro OFF ? Tous les faits compilés pertinents sont introduits ;
le compilateur affiche ce qui manque. -/
theorem probe_collective_contact_rigidity (C : OffCarrier) (I : PrimeGapInterval)
    (hI : zeroPoint C.zero ∈ crowd I) : False := by
  -- demande exacte de l'écart = foule + queue (toute position radiale)
  have hDecomp := crowd_tail_decomposition I
  -- le terme du zéro OFF est isolé dans la part de foule (somme finie)
  have hSplit := C.crowdSum_split_zero I hI
  -- borne de la queue, indépendante du résidu, exposant 1, sans RH
  have hTail := collective_residual_bound I
  -- le miroir est dans la même foule, même pas, contacts décalés d'une quantité non nulle
  have hMirror := (C.mirror_mem_crowd_iff I).mpr hI
  have hShift := contactLog_shift_ne_zero_of_radial_ne (z := C.zero) (w := mirrorMember C.zero)
    (mirrorMember_ordinate C.zero).symm (by
      rw [mirrorMember_radial]
      have := C.zero_low
      intro h; linarith) 0
  -- les contacts du zéro OFF rendent ses deux coordonnées
  have hCoord := coordinates_from_two_contacts C.zero 0
  -- amplitude : la densité du miroir domine celle du zéro OFF en tout x > 1
  have hAmp := C.mirror_density_dominates I.one_lt_upper
  -- un membre de la foule traverse au plus un contact dans l'écart
  have hCross := contactsCrossed_le_one_of_mem_crowd C.zero I hI
  -- la foule seule n'accomplit jamais la demande (F8)
  have hF8 := crowd_alone_never_accomplishes_demand I.rank
  -- position radiale basse
  have hLow := C.zero_low
  done

/-- Contrôle d'identification (PAS une preuve) : le but en hypothèse ferme la conclusion. -/
theorem control_goal_closes (C : OffCarrier) (hMissing : rZeroRadialPosition C.zero.1 = 1 / 2) : False := by
  have := C.zero_low
  linarith

end RHV6Fresh

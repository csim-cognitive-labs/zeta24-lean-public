> Version française conservée à titre de référence. Main language: English, see README.md.

# E421 — Entrelacement des contacts de Tours différentes sur le même axe réel (pré-enregistrée 2026-11-03)

Objectif : décrire, sans premiers ni écarts ni cellules entières, comment les contacts de Tours de hauteurs différentes
s'entrelacent sur l'axe réel : nombre de contacts d'une Tour entre deux contacts consécutifs d'une autre, décalages, coïncidences,
et sensibilité radiale de l'entrelacement (Tour synthétique séparée, jamais à la hauteur d'un zéro réel).

Prédictions (module Lean `ContactRealValue.lean`, écrites avant exécution) :
* entre deux contacts consécutifs de (β₁,T₁) il y a ⌊T₂/T₁⌋ ou ⌈T₂/T₁⌉ contacts de (β₂,T₂) (pas logarithmiques π/T₁, π/T₂) ;
* décalage exact : log C_j^{(2)} − log C_k^{(1)} = (φ₂ + jπ)/T₂ − (φ₁ + kπ)/T₁ ;
* la position radiale n'entre que par φ(β) = arctan(T/β) ∈ (0, π/2) ; le déplacement d'un contact de β à ½ vaut
  (φ(β) − φ(½))/T, de module < π/(2T) : moins d'un demi-pas ; le comptage des contacts entre deux contacts d'une autre Tour
  est donc aveugle à β à une unité près, et l'ordre d'entrelacement peut changer d'au plus un cran par contact ;
* deux contacts d'une paire miroir (β, 1−β) à même hauteur coïncident si et seulement si β = ½ (arctan injective).
Aucune de ces prédictions n'est lue comme une exclusion des zéros OFF.

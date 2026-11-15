# E434 — Résultats (2026-11-04)

Pré-enregistrement : commit 30353022. Compilation seule, aucun jumeau requis.

## Sondes (`BoundaryContactProbe_SCRATCH.lean`, supprimé après capture)
- Tentative 0 (`logs/probe_attempt0_env_missing_olean.txt`) : erreur d'environnement seule — le module isolé E433
  n'avait pas d'objet compilé (il n'est pas dans `RHV6Fresh.lean`) ; construit par `lake build
  RHV6Fresh.Terminal.PacketSeriesBalance`. Aucune erreur Lean.
- Tentative 1 (`logs/probe_attempt1.txt`) : toutes les déclarations passent ; seul le but de sonde reste.

### S1 — « complément silencieux sur la fenêtre, et les deux bords `a`, `a+m` sont des contacts du zéro ⟹ False »
But laissé (exact dans le journal) : `0 = Σ Λ(a+k+1) − Re(variation du pas du fond) − effet de bords`, où aux
abscisses `a` et `a+m` la lecture du zéro se réduit à la valeur au contact × croissance × `(β+1)/‖ρ+1‖²` (cosinus à 1,
sinus à 0) tandis que la lecture du miroir garde ses deux termes (sa fraction de cellule n'est pas nulle : les contacts
du miroir ne sont pas ceux du zéro, décalage `(arctan(T/(1−β)) − arctan(T/β))/π`), et où les abscisses `a+1`, `a+m+1`
restent lues par leurs propres derniers contacts. Pas de contradiction. Conforme à l'attendu : le contenu
arithmétique de la fenêtre est mis face à une combinaison de valeurs aux contacts des deux membres.

## Module `Terminal/BoundaryContactReading.lean` (isolé, 11 déclarations, aucun `sorry`)
- Une tentative (`logs/lean_attempt1.txt`, EXIT=0) ; 5 `#print axioms` standards.
- `towerIm`, `towerIm_eq_im`, `towerIm_from_lastContact` ; `integratedTower_re_eq`,
  `integratedTower_re_from_lastContact` ; `zeroPoint_mk`, `zeroTerm_div_eq_integrated`, `pairPrimitive_re`,
  `mirror_height_eq`, `pairPrimitive_re_from_contacts`, `pair_window_re_balance`.
- `lake build RHV6Fresh` : « Build completed successfully », EXIT=0 (`logs/lake_build_full_trimmed.txt`).

## Verdict
L'effet de bords de la paire est entièrement lu par les contacts des deux membres : valeur au dernier contact,
croissance sur la fraction de cellule, et un retard d'angle propre au canal intégré (poids `β+1` et `T`), différent
pour le zéro (`1/2 − δ`) et pour le miroir (`1/2 + δ`). Le bilan de fenêtre met le contenu arithmétique (poids de von
Mangoldt) face à ces lectures. Aucune contradiction ; le chaînon restant est inchangé (exposant du reste), mais il est
maintenant écrit dans le vocabulaire des contacts.

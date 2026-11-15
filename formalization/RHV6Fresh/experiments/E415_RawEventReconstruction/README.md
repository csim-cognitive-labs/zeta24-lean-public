# E415 — Reconstruction des poids arithmétiques depuis le signal spectral (pré-enregistrée le 2026-11-03)

**Question.** Les poids Λ(n) sont-ils retrouvés depuis les seuls zéros (et les termes analytiques de la formule), sans
accès aux valeurs arithmétiques, et avec quelle erreur selon la troncature ?

**Approches comparées.** A : canal brut aux demi-entiers, Λ̂ᴬ_H(n) = ψ̂₀_H(n+½) − ψ̂₀_H(n−½) (prémisse `RawExplicitFormulaAt`,
non compilée). B : canal intégré, seconde différence Λ̂ᴮ_H(n) = ψ̂₁_H(n+1) − 2ψ̂₁_H(n) + ψ̂₁_H(n−1) (théorème compilé
`reconstructedVonMangoldt_eq`, limite `reconstructedVonMangoldt_eq_limit_contact_accumulation`). C : accumulation
par contacts à valeurs complexes (égale à D par télescopage, vérifié explicitement sur 5000 zéros). D : somme spectrale
directe (= B).

**Interdits.** Λ(n), les premiers et les écarts n'entrent dans aucun calcul de Λ̂ ; ils sont chargés APRÈS, pour la
validation seulement (`sieve_lambda`, marqué VALIDATION). Aucune méthode n'est sélectionnée d'après les résultats.

**Résultats.** `RESULTS.md`, `data/e415_results.json`, `data/e415_W*_full.txt`, `data/lam{A,B}_W*.npy`, `logs/e415.log`.

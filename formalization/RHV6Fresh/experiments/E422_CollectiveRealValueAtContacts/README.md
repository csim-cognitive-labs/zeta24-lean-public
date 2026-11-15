# E422 — Somme collective des valeurs réelles aux contacts (pré-enregistrée 2026-11-03)

Définition précise (fixée avant exécution). Famille F = les N premiers zéros, posés sur la ligne, avec conjugués (facteur 2·Re).
Pour une Tour ρ₀ ∈ F et un de ses contacts x = C_k(ρ₀) :
* valeur propre : 2·v_k(ρ₀) = 2·(−1)^k C_k^β/|ρ₀| (réelle par construction, la conjuguée donne la même valeur) ;
* contributions des autres Tours **évaluées à la même position x** : 2·Re(x^ρ/ρ) pour ρ ∈ F ∖ {ρ₀} ; ce sont des valeurs hors
  contact en général (Im(x^ρ/ρ) ≠ 0), seule la partie réelle entre dans la somme (famille stable par conjugaison) ;
* somme collective S_F(x) = 2·v_k(ρ₀) + Σ_{ρ ≠ ρ₀} 2·Re(x^ρ/ρ) = Σ_{ρ ∈ F} 2·Re(x^ρ/ρ), évaluée aux positions des contacts.
Aucune fonction arithmétique n'est utilisée : les sommes sont comparées entre elles (part de la valeur propre, signe, variation
avec N), jamais à ψ, aux premiers ou à li.
Mesures prévues : S_F aux contacts des Tours 1, 2, 3, 100, 1000 dans [100, 1000], pour N ∈ {10, 100, 1 000, 10⁴, 10⁵, 2 001 052} ;
part |2v_k|/|S_F| ; accord de signe entre v_k et S_F ; S_F − 2v_k (les autres) ; phase des autres Tours à x (fraction de π) ;
variation de S_F entre N et le N suivant aux mêmes points. Identité de contrôle : S_F(C_{k+1}) − S_F(C_k) = Σ_ρ 2Re[F(C_{k+1}) − F(C_k)]
(télescopage, déjà compilé) n'est PAS re-mesurée.

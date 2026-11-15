# Suites préparées et liste du 16 novembre 2026

## 1. Message de paix, version anglaise
> Peace, brotherhood and blessing to everyone who reads these lines. Whatever name each of us gives to the One who created us, we are one family of earthlings. Come and break bread with us: you are all welcome in our humble home. Mathematicians have always shared their knowledge, across all peoples and all ages. We stand humbly in that long chain. This project is disinterested: our hope is that AI benefits the whole world, especially those who have nothing. Honesty first: the Riemann Hypothesis is not proved, and this repository never claims otherwise.

## 2. Question pour Lean Zulip (canal « new members », puis « general »), en anglais
> **Title:** Feedback wanted on a Lean 4 formalization approaching RH through prime gaps (RHV6Fresh, builds green, conditional terminal theorem)
> Hello, I am Charles S. We published github.com/csim-cognitive-labs/zeta24-lean-public: a Lean 4 + Mathlib project (pinned Mathlib rev 51e6992e, Lean v4.33.0-rc2) that relates prime gaps, "Towers" of zero contacts and shared primes. `lake build RHV6Fresh` is green; the only theorem concluding RH is conditional on a hypothesis we prove equivalent to RH, so RH is NOT proved and nothing is assumed silently. We reuse code from anthropics/formal-math (zeta23) and PrimeNumberTheoremAnd under Apache 2.0, with notices. Concrete question: what arithmetic constraint does the exact reconstruction of a gap between two consecutive primes impose on a first off-line Tower, that its contacts and those of its mirror cannot satisfy? Corrections, reviews and pointers are very welcome. Licence: proprietary, strictly non-commercial (see LICENSE).

## 3. Notes de la release v1.0.0 (à coller dans GitHub Releases)
**zeta24-lean v1.0.0 — 15 novembre 2026.** Premier export public. Formalisation Lean RHV6Fresh et rhv3_lean, trois documents maîtres, expériences E400 à E477. Build vérifié depuis zéro : `lake build RHV6Fresh`, 9 064 tâches, sortie 0, axiomes standard seulement. L'hypothèse de Riemann n'est pas démontrée ; le théorème terminal est conditionnel. © Charles S., enveloppe Soleau INPI DSO2026044645 (15/11/2026, 18:14:32 UTC). Licence propriétaire à usage non commercial strict. Composants tiers Apache 2.0 : THIRD_PARTY_NOTICES.md.

## 4. Votre liste de demain
**Sécurité du dépôt public (15 min)**
1. Réglages du dépôt, Rules : protéger `main` (pas de force push, pas de suppression, pull request obligatoire).
2. Activer Secret scanning et Push protection ; Actions : permissions en lecture seule.
3. Compte GitHub : passkey ou clé de sécurité, double authentification obligatoire.
4. Vérifier que le dépôt privé n'a plus de visibilité publique par erreur.

**Antériorité (30 min)**
5. Créer la release v1.0.0 (notes ci-dessus) ; si vous voulez un DOI, relier le dépôt à Zenodo avant de la publier.
6. Conserver l'accusé de l'enveloppe Soleau (PDF) hors dépôt, en deux copies.
7. Faire sauvegarder le dépôt privé en clone miroir (`git clone --mirror`).

**Diffusion (1 h)**
8. Créer la Page LinkedIn « CSIM Cognitive Labs » avec le texte de docs/PROPOSITIONS_COMMUNICATION_20261115.md.
9. Poster l'annonce (docs/ANNONCE_PUBLICATION_20261115.md) : faites relire le brouillon une fois.
10. Poster l'issue courtoise sur anthropics/formal-math (texte dans les propositions) : une seule fois, sans commentaires promotionnels.
11. Poster la question sur Lean Zulip (texte ci-dessus).

**Décisions qui vous attendent (pas urgentes)**
12. Historique du dépôt privé : réécrire ou non (trailers Anthropic, e-mail dans 25 fichiers d'exécution). Je ne le ferai pas sans ordre.
13. Workflows du dépôt privé qui écrivent sur `main` : les garder ou non.
14. Un avocat ou le service propriété intellectuelle de l'INPI pour valider la licence (droit français, cession des contributions).
15. Si des relecteurs répondent : je traiterai issues et pull requests, et rédigerai les réponses.

/-
Porté de AlexKontorovich/PrimeNumberTheoremAnd (révision 127b50e3, Apache 2.0, voir LICENSE et PROVENANCE.md),
fichier PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean ; attributs et commandes du blueprint (LeanArchitect) retirés, imports renommés.
-/
import Mathlib.Algebra.Notation.Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function

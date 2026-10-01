import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}

theorem alternatingDual_zero_any_slot (V : Submodule ℂ M)
    (F : (Module.Dual ℂ M) [⋀^Fin (n + 1)]→ₗ[ℂ] ℂ)
    (hF : ∀ v, (∀ p ∈ V, v 0 p = 0) → F v = 0)
    (v : Fin (n + 1) → Module.Dual ℂ M) (i : Fin (n + 1))
    (hv : ∀ p ∈ V, v i p = 0) : F v = 0 := by
  by_cases hi : i = 0
  · exact hF v (hi ▸ hv)
  · have h := hF (v ∘ Equiv.swap 0 i) (by simpa only [Function.comp_apply,
      Equiv.swap_apply_left] using hv)
    rw [F.map_swap v (Ne.symm hi)] at h
    exact neg_eq_zero.mp h

theorem alternatingDual_update_eq (V : Submodule ℂ M)
    (F : (Module.Dual ℂ M) [⋀^Fin (n + 1)]→ₗ[ℂ] ℂ)
    (hF : ∀ v, (∀ p ∈ V, v 0 p = 0) → F v = 0)
    (v : Fin (n + 1) → Module.Dual ℂ M) (i : Fin (n + 1))
    (a b : Module.Dual ℂ M) (hab : ∀ p ∈ V, a p = b p) :
    F (Function.update v i a) = F (Function.update v i b) := by
  have h := alternatingDual_zero_any_slot V F hF (Function.update v i (a - b)) i (by
    intro p hp
    simp [hab p hp])
  rw [F.map_update_sub] at h
  exact sub_eq_zero.mp h

/-- An alternating form whose first contractions lie in a subspace depends
    only on the restrictions of its dual arguments to that subspace.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem alternatingDual_eq_of_restrictions (V : Submodule ℂ M)
    (F : (Module.Dual ℂ M) [⋀^Fin (n + 1)]→ₗ[ℂ] ℂ)
    (hF : ∀ v, (∀ p ∈ V, v 0 p = 0) → F v = 0)
    (v w : Fin (n + 1) → Module.Dual ℂ M)
    (hvw : ∀ i p, p ∈ V → v i p = w i p) : F v = F w := by
  have hs (s : Finset (Fin (n + 1))) :
      F (fun i => if i ∈ s then w i else v i) = F v := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, ite_false]
    | @insert i s hi ih =>
      have h₁ : (fun j => if j ∈ insert i s then w j else v j) =
          Function.update (fun j => if j ∈ s then w j else v j) i (w i) := by
        funext j
        by_cases hj : j = i <;> simp [hj, hi]
      have h₂ : Function.update (fun j => if j ∈ s then w j else v j) i (v i) =
          (fun j => if j ∈ s then w j else v j) := by
        funext j
        by_cases hj : j = i <;> simp [hj, hi]
      rw [h₁, alternatingDual_update_eq V F hF _ i (w i) (v i)
        (fun p hp => (hvw i p hp).symm), h₂, ih]
  simpa only [Finset.mem_univ, ite_true] using (hs Finset.univ).symm

theorem alternatingDual_descent (V : Submodule ℂ M)
    (F : (Module.Dual ℂ M) [⋀^Fin (n + 1)]→ₗ[ℂ] ℂ)
    (hF : ∀ v, (∀ p ∈ V, v 0 p = 0) → F v = 0) :
    F = (F.compLinearMap (Subspace.dualLift V)).compLinearMap V.dualRestrict := by
  apply AlternatingMap.ext
  intro v
  apply alternatingDual_eq_of_restrictions V F hF
  intro i p hp
  rw [Subspace.dualLift_of_mem hp]
  rfl

theorem alternatingDual_descent_ne_zero (V : Submodule ℂ M)
    (F : (Module.Dual ℂ M) [⋀^Fin (n + 1)]→ₗ[ℂ] ℂ)
    (hF : ∀ v, (∀ p ∈ V, v 0 p = 0) → F v = 0) (hne : F ≠ 0) :
    F.compLinearMap (Subspace.dualLift V) ≠ 0 := by
  intro hz
  apply hne
  rw [alternatingDual_descent V F hF, hz, AlternatingMap.zero_compLinearMap]

end
end ModifiedCartan

#print axioms ModifiedCartan.alternatingDual_descent

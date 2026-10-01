import ModifiedCartan.CentralCharacterOperator
import Mathlib.Algebra.Module.Submodule.RestrictScalars

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {G M N : Type*} [Group G] [Fintype G]
  [AddCommGroup M] [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M]
  [AddCommGroup N] [Module ℂ N]

theorem complex_submodule_eq_top_of_contains_group_simples
    (K : Submodule ℂ M)
    (hK : ∀ S : Submodule ℂ[G] M, IsSimpleModule ℂ[G] S → S.restrictScalars ℂ ≤ K) :
    K = ⊤ := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_ne_zero (α := G))⟩
  have hs := congrArg (Submodule.restrictScalars ℂ)
    (IsSemisimpleModule.sSup_simples_eq_top ℂ[G] M)
  rw [Submodule.restrictScalars_sSup, Submodule.restrictScalars_top] at hs
  apply le_antisymm le_top
  rw [← hs]
  apply sSup_le
  rintro S ⟨T, hT, rfl⟩
  exact hK T hT

/-- A linear identity can be checked on the simple group-algebra submodules. -/
theorem linearMap_eq_zero_of_group_simples (f : M →ₗ[ℂ] N)
    (hf : ∀ S : Submodule ℂ[G] M, IsSimpleModule ℂ[G] S →
      ∀ v ∈ S, f v = 0) : f = 0 := by
  have hk : LinearMap.ker f = ⊤ :=
    complex_submodule_eq_top_of_contains_group_simples (LinearMap.ker f)
      (fun S hS v hv => hf S hS v hv)
  apply LinearMap.ext
  intro v
  have hv : v ∈ LinearMap.ker f := by rw [hk]; trivial
  exact hv

end
end ModifiedCartan



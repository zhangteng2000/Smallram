import ModifiedCartan.PositiveGeometricSum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def finiteCompositionMonomialSum {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [CommSemiring R] (ℓ : A → ℕ) (x : B → R) : R :=
  ∑ κ : (a : A) → Fin (ℓ a), ∑ f : A ↪ B, ∏ a : A, x (f a) ^ ((κ a).val + 1)

theorem finiteCompositionMonomialSum_eq {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [CommSemiring R] (ℓ : A → ℕ) (x : B → R) :
    finiteCompositionMonomialSum ℓ x =
      ∑ f : A ↪ B, ∏ a : A, positiveGeometricSum (ℓ a) (x (f a)) := by
  rw [finiteCompositionMonomialSum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  exact (Fintype.prod_sum (fun a (r : Fin (ℓ a)) => x (f a) ^ (r.val + 1))).symm

end
end ModifiedCartan



import ModifiedCartan.CycleColorings
import ModifiedCartan.FixedPointPermutationSums
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def permutationCycleWeight (σ : Equiv.Perm A) (κ : A → ℕ) (c : PermutationCycles σ) : ℕ :=
  ∑ i ∈ (Finset.univ : Finset A).filter (fun i => permutationCycleClass σ i = c), κ i

theorem coloring_product_eq_cycle_product {B R : Type*} [CommMonoid R]
    (σ : Equiv.Perm A) (κ : A → ℕ) (x : B → R) (F : PermutationCycles σ → B) :
    (∏ i : A, x (F (permutationCycleClass σ i)) ^ κ i) =
      ∏ c : PermutationCycles σ, x (F c) ^ permutationCycleWeight σ κ c := by
  calc
    _ = ∏ c : PermutationCycles σ,
        ∏ i ∈ (Finset.univ : Finset A).filter (fun i => permutationCycleClass σ i = c),
          x (F (permutationCycleClass σ i)) ^ κ i :=
      (Finset.prod_fiberwise Finset.univ (permutationCycleClass σ)
        (fun i => x (F (permutationCycleClass σ i)) ^ κ i)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro c hc
      rw [permutationCycleWeight, ← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

/-- Exact finite-variable weighted cycle power sums, with fixed points included. -/
theorem fixed_coloring_sum_eq_cycle_powers {B R : Type*} [Fintype B] [CommSemiring R]
    (σ : Equiv.Perm A) (κ : A → ℕ) (x : B → R) :
    (∑ f : A → B, if ∀ i, f (σ i) = f i then ∏ i : A, x (f i) ^ κ i else 0) =
      ∏ c : PermutationCycles σ, ∑ b : B, x b ^ permutationCycleWeight σ κ c := by
  calc
    _ = ∑ f : {f : A → B // ∀ i, f (σ i) = f i}, ∏ i : A, x (f.val i) ^ κ i :=
      sum_dite_eq_sum_subtype (fun f : A → B => ∀ i, f (σ i) = f i)
        (fun f _ => ∏ i : A, x (f i) ^ κ i)
    _ = ∑ F : PermutationCycles σ → B, ∏ i : A,
        x (F (permutationCycleClass σ i)) ^ κ i :=
      (Equiv.sum_comp (cycleColoringEquiv σ B)
        (fun f => ∏ i : A, x (f.val i) ^ κ i)).symm
    _ = ∑ F : PermutationCycles σ → B,
        ∏ c : PermutationCycles σ, x (F c) ^ permutationCycleWeight σ κ c := by
      apply Finset.sum_congr rfl
      intro F hF
      exact coloring_product_eq_cycle_product σ κ x F
    _ = _ := (Fintype.prod_sum (fun c b => x b ^ permutationCycleWeight σ κ c)).symm

end
end ModifiedCartan



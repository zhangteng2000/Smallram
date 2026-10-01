import ModifiedCartan.SigmaPermutationSign
import ModifiedCartan.BlockInflationPowerSums
import ModifiedCartan.ScaledMonomialPowerSums

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem blockInflation_sign_complex {A : Type*} [Fintype A] [DecidableEq A]
    (κ : A → ℕ) (σ : Equiv.Perm A) :
    ((Equiv.Perm.sign (blockInflation κ σ) : ℤ) : ℂ) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (-1 : ℂ) ^ (∑ a, κ a) := by
  rw [blockInflation_sign]
  simp

/-- Signed cycle power sums for all ways of joining the prescribed blocks.
The sign and cycle lengths both come from the constructed permutation. -/
theorem signed_blockInflation_cycle_power_sum {A B R : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [CommRing R] [Algebra ℂ R]
    (κ : A → ℕ) (x : B → R) :
    (∑ σ : Equiv.Perm A, ((Equiv.Perm.sign (blockInflation κ σ) : ℤ) : ℂ) •
      ∏ c : PermutationCycles (blockInflation κ σ),
        ∑ b : B, x b ^ permutationCycleWeight (blockInflation κ σ) (fun _ => 1) c) =
    (-1 : ℂ) ^ (∑ a, κ a) •
      ∑ f : A → B, if Function.Injective f then ∏ a, x (f a) ^ (κ a + 1) else 0 := by
  calc
    _ = ∑ σ : Equiv.Perm A, (-1 : ℂ) ^ (∑ a, κ a) •
        (((Equiv.Perm.sign σ : ℤ) : ℂ) •
          ∏ c : PermutationCycles σ, ∑ b : B,
            x b ^ permutationCycleWeight σ (fun a => κ a + 1) c) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [blockInflation_sign_complex κ σ, blockInflation_cycle_power_sums κ σ x,
        mul_comm, mul_smul]
    _ = _ := by
      rw [← Finset.smul_sum, ← distinct_color_sum_eq_signed_cycle_powers (fun a => κ a + 1) x]

end
end ModifiedCartan


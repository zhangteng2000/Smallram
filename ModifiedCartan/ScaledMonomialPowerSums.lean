import ModifiedCartan.SignedFixedColorings
import ModifiedCartan.CycleWeightedPowers
import Mathlib.Algebra.MvPolynomial.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem distinct_color_sum_eq_signed_cycle_powers {A B R : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [CommRing R] [Algebra ℂ R]
    (κ : A → ℕ) (x : B → R) :
    (∑ f : A → B, if Function.Injective f then ∏ i : A, x (f i) ^ κ i else 0) =
      ∑ σ : Equiv.Perm A, ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ∏ c : PermutationCycles σ, ∑ b : B, x b ^ permutationCycleWeight σ κ c := by
  calc
    _ = ∑ σ : Equiv.Perm A, ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ∑ f : A → B, if ∀ i, f (σ i) = f i then ∏ i : A, x (f i) ^ κ i else 0 :=
      (signed_fixed_coloring_sum (fun f : A → B => ∏ i : A, x (f i) ^ κ i)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [fixed_coloring_sum_eq_cycle_powers]

def scaledMonomialPolynomial {A : Type*} [Fintype A] [DecidableEq A] (B : Type*) [Fintype B]
    (κ : A → ℕ) : MvPolynomial B ℂ :=
  ∑ f : A → B, if Function.Injective f then ∏ i : A, MvPolynomial.X (f i) ^ κ i else 0

/-- Exact finite-variable version of KP source Proposition 2.23, proved from
signed stabilizer cancellation and the actual complete cycle partition. -/
theorem scaledMonomialPolynomial_power_sum {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (κ : A → ℕ) :
    scaledMonomialPolynomial B κ =
      ∑ σ : Equiv.Perm A, MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
        ∏ c : PermutationCycles σ, ∑ b : B,
          MvPolynomial.X b ^ permutationCycleWeight σ κ c := by
  simpa only [scaledMonomialPolynomial, MvPolynomial.smul_eq_C_mul] using
    distinct_color_sum_eq_signed_cycle_powers κ (fun b : B => (MvPolynomial.X b : MvPolynomial B ℂ))

end
end ModifiedCartan



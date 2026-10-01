import ModifiedCartan.InjectiveColorSums
import ModifiedCartan.ScaledMonomialPowerSums
import Mathlib.Algebra.MvPolynomial.Rename

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem scaledMonomialPolynomial_rename {A B C : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] (κ : A → ℕ) (r : B → C) :
    MvPolynomial.rename r (scaledMonomialPolynomial B κ) =
      ∑ f : A → B, if Function.Injective f then
        ∏ i : A, (MvPolynomial.X (r (f i)) : MvPolynomial C ℂ) ^ κ i else 0 := by
  rw [scaledMonomialPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hi : Function.Injective f
  · simp only [ite_eq_left hi, map_prod, map_pow, MvPolynomial.rename_X]
  · simp only [ite_eq_right hi, map_zero]

/-- Exact finite-variable alphabet-addition identity needed for the Bernstein
operator in KP source Proposition 2.22. -/
theorem scaledMonomialPolynomial_add_variable {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] (κ : A → ℕ) :
    scaledMonomialPolynomial (Option B) κ =
      MvPolynomial.rename some (scaledMonomialPolynomial B κ) +
        ∑ a : A, (MvPolynomial.X (none : Option B)) ^ κ a *
          MvPolynomial.rename some (scaledMonomialPolynomial B (fun i : {i : A // i ≠ a} => κ i.val)) := by
  let u : A → MvPolynomial (Option B) ℂ := fun a => MvPolynomial.X none ^ κ a
  let w : A → B → MvPolynomial (Option B) ℂ := fun a b => MvPolynomial.X (some b) ^ κ a
  have hw (i : A) (b : Option B) : extraColorWeight u w i b = MvPolynomial.X b ^ κ i := by
    cases b <;> rfl
  have hh := sum_injective_extra_color u w
  simp_rw [hw] at hh
  simp_rw [scaledMonomialPolynomial_rename]
  dsimp only [u, w] at hh
  unfold scaledMonomialPolynomial
  convert! hh using 1
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hi : Function.Injective f
  · simp only [ite_eq_left hi]
  · simp only [ite_eq_right hi]

end
end ModifiedCartan



import ModifiedCartan.SignedColorStabilizer
import Mathlib.Algebra.Module.BigOperators

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The signed fixed-coloring sum selects exactly the injective colorings.
This is the finite combinatorial cancellation behind KP source Proposition 2.23. -/
theorem signed_fixed_coloring_sum {A B V : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [AddCommGroup V] [Module ℂ V] (w : (A → B) → V) :
    (∑ σ : Equiv.Perm A, ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ∑ f : A → B, if ∀ i, f (σ i) = f i then w f else 0) =
        ∑ f : A → B, if Function.Injective f then w f else 0 := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  calc
    _ = (∑ σ : Equiv.Perm A,
        if ∀ i, f (σ i) = f i then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0) • w f := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro σ hσ
      split_ifs <;> simp
    _ = _ := by
      rw [signed_color_stabilizer_sum]
      split_ifs <;> simp

end
end ModifiedCartan



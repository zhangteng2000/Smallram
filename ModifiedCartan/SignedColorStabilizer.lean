import ModifiedCartan.FiniteInvolutionSum
import Mathlib.GroupTheory.Perm.Sign

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {A B : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] in
theorem coloring_swap_eq (f : A → B) (a b : A) (hab : f a = f b) (x : A) :
    f (Equiv.swap a b x) = f x := by
  by_cases ha : x = a
  · subst x
    simpa only [Equiv.swap_apply_left] using hab.symm
  · by_cases hb : x = b
    · subst x
      simpa only [Equiv.swap_apply_right] using hab
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Signed cancellation in the stabilizer of an actual finite coloring. -/
theorem signed_color_stabilizer_sum (f : A → B) :
    (∑ σ : Equiv.Perm A, if ∀ i, f (σ i) = f i then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0) =
      if Function.Injective f then 1 else 0 := by
  by_cases hf : Function.Injective f
  · rw [ite_eq_left hf, Finset.sum_eq_single (1 : Equiv.Perm A)]
    · simp
    · intro σ hσ hne
      have hh : ¬∀ i, f (σ i) = f i := by
        intro he
        exact hne (Equiv.ext (fun i => hf (he i)))
      rw [ite_eq_right hh]
    · simp
  · rw [ite_eq_right hf]
    have hn := hf
    change ¬∀ a b, f a = f b → a = b at hn
    push Not at hn
    obtain ⟨a, b, hab, hne⟩ := hn
    let F : Equiv.Perm A → ℂ :=
      fun σ => if ∀ i, f (σ i) = f i then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0
    have he (σ : Equiv.Perm A) : F (Equiv.swap a b * σ) = -F σ := by
      have hp : (∀ i, f ((Equiv.swap a b * σ) i) = f i) ↔ ∀ i, f (σ i) = f i := by
        simp only [Equiv.Perm.mul_apply, coloring_swap_eq f a b hab]
      simp only [F, hp, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
      split_ifs <;> simp
    have hs : (∑ σ, F σ) = -(∑ σ, F σ) := by
      calc
        _ = ∑ σ, F (Equiv.swap a b * σ) :=
          (Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b)) F).symm
        _ = _ := by simp only [he, Finset.sum_neg_distrib]
    have htwo : (2 : ℂ) * (∑ σ, F σ) = 0 := by
      simpa only [two_mul] using (eq_neg_iff_add_eq_zero.mp hs)
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end
end ModifiedCartan



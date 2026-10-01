import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Complex.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Sum an antisymmetric function using one representative of each nonzero
involution orbit. The complement contributes zero by the stated pointwise fact. -/
theorem sum_involution_cut {X V : Type*} [Fintype X] [AddCommGroup V] [Module ℂ V]
    (e : X ≃ X) (he : ∀ x, e (e x) = x) (p : X → Prop) [DecidablePred p]
    (hp : ∀ x, p x → ¬p (e x)) (c : X → V) (hc : ∀ x, c (e x) = -c x)
    (hz : ∀ x, ¬p x → ¬p (e x) → c x = 0) (w : X → ℂ) :
    (∑ x, w x • c x) = ∑ x, if p x then (w x - w (e x)) • c x else 0 := by
  have hsplit (x : X) : w x • c x =
      (if p x then w x • c x else 0) + (if p (e x) then w x • c x else 0) := by
    by_cases hx : p x
    · simp only [if_pos hx, if_neg (hp x hx), add_zero]
    · by_cases hy : p (e x)
      · simp only [if_neg hx, if_pos hy, zero_add]
      · simp only [if_neg hx, if_neg hy, hz x hx hy, smul_zero, add_zero]
  have hr : (∑ x, if p (e x) then w x • c x else 0) =
      ∑ x, if p x then -(w (e x) • c x) else 0 := by
    simpa only [he, hc, smul_neg] using
      (e.sum_comp (fun x => if p (e x) then w x • c x else 0)).symm
  calc
    _ = ∑ x, ((if p x then w x • c x else 0) +
        (if p (e x) then w x • c x else 0)) := Finset.sum_congr rfl (fun x _ => hsplit x)
    _ = (∑ x, if p x then w x • c x else 0) +
        ∑ x, if p x then -(w (e x) • c x) else 0 := by rw [Finset.sum_add_distrib, hr]
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : p x <;> simp [hx, sub_eq_add_neg, add_smul]

end
end ModifiedCartan



import ModifiedCartan.FiniteRowMinimum
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Order.Preorder.Finite

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem fin_strictMono_weighted_sum_perm_le {n : ℕ} (f : Fin n → ℕ)
    (hf : StrictMono f) (σ : Equiv.Perm (Fin n)) :
    (∑ i : Fin n, (σ i).val * f i) ≤ ∑ i : Fin n, i.val * f i := by
  have hm : Monovary (fun i : Fin n => i.val) f := by
    intro i j hij
    exact (hf.lt_iff_lt.mp hij).le
  exact hm.sum_comp_perm_mul_le_sum_mul (σ := σ)

/-- For strictly increasing labels, equality in rearrangement forces the
finite row permutation to be the identity. -/
theorem fin_strictMono_weighted_sum_perm_lt {n : ℕ} (f : Fin n → ℕ)
    (hf : StrictMono f) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
    (∑ i : Fin n, (σ i).val * f i) < ∑ i : Fin n, i.val * f i := by
  have hm : Monovary (fun i : Fin n => i.val) f := by
    intro i j hij
    exact (hf.lt_iff_lt.mp hij).le
  apply (hm.sum_comp_perm_mul_lt_sum_mul_iff (σ := σ)).mpr
  intro h
  apply hσ
  have hs : StrictMono σ := by
    intro i j hij
    have hle : σ i ≤ σ j := h (hf hij)
    apply lt_of_le_of_ne hle
    intro he
    exact hij.ne (σ.injective he)
  apply Equiv.ext
  intro i
  exact congrFun hs.eq_id i

end
end ModifiedCartan



import ModifiedCartan.ZeroCopiesCount
import ModifiedCartan.ReciprocalTailIntegral
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped Topology BigOperators
open Filter Set Metric Function
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `eq:reciprocal-tail` for the actual repeated zero divisor,
derived from its counting bound. The next wrapper derives that bound
from the entire-function order. -/
theorem entire_reciprocal_tail_of_count_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {σ C R : ℝ} (hC : 0 ≤ C) (hσ : σ < 1) (hR : 1 ≤ R)
    (hc : ∀ t, 1 ≤ t → zeroCount f t ≤ C * t ^ σ) :
    Summable (fun a : entireZeroCopies f => if R < ‖a.1‖ then ‖a.1‖⁻¹ else 0) ∧
      (∑' a : entireZeroCopies f, if R < ‖a.1‖ then ‖a.1‖⁻¹ else 0) ≤
        (C / (1 - σ)) * R ^ (σ - 1) := by
  classical
  have hn : 0 ≤ (fun a : entireZeroCopies f => if R < ‖a.1‖ then ‖a.1‖⁻¹ else 0) := by
    intro a
    dsimp only [Pi.zero_apply]
    split_ifs <;> positivity
  have hb (S : Finset (entireZeroCopies f)) :
      (∑ a ∈ S, if R < ‖a.1‖ then ‖a.1‖⁻¹ else 0) ≤ (C / (1 - σ)) * R ^ (σ - 1) := by
    let T := S.filter (fun a => R < ‖a.1‖)
    have hT := finite_reciprocal_tail_bound T (fun a => ‖a.1‖)
      (zero_lt_one.trans_le hR) hC hσ
      (fun a ha => (Finset.mem_filter.mp ha).2.le) (fun t ht =>
        (finite_zero_copies_count_le hf (zero_le_one.trans (hR.trans ht)) T).trans
          (hc t (hR.trans ht)))
    simpa only [T, Finset.sum_filter] using hT
  exact ⟨summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

theorem entire_reciprocal_roots_summable_of_count_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {σ C : ℝ} (hC : 0 ≤ C) (hσ : σ < 1)
    (hc : ∀ t, 1 ≤ t → zeroCount f t ≤ C * t ^ σ) :
    Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹) := by
  classical
  have hfinite : {a : entireZeroCopies f | ‖a.1‖ ≤ 1}.Finite :=
    @Set.toFinite (entireZeroCopies f) {a | ‖a.1‖ ≤ 1}
      (zeroCopiesInClosedBall_finite hf zero_le_one)
  have hhead : Summable (fun a : entireZeroCopies f => if ‖a.1‖ ≤ 1 then ‖a.1‖⁻¹ else 0) := by
    apply summable_of_hasFiniteSupport
    apply hfinite.subset
    intro a ha
    by_contra h
    change ¬ ‖a.1‖ ≤ 1 at h
    exact ha (by simp [h])
  have htail := (entire_reciprocal_tail_of_count_bound hf hC hσ le_rfl hc).1
  apply (hhead.add htail).congr
  intro a
  by_cases ha : ‖a.1‖ ≤ 1
  · simp [ha, not_lt.mpr ha]
  · simp [ha, lt_of_not_ge ha]

end ModifiedCartan
#print axioms ModifiedCartan.entire_reciprocal_tail_of_count_bound
#print axioms ModifiedCartan.entire_reciprocal_roots_summable_of_count_bound

import ModifiedCartan.ReciprocalRoots
import ModifiedCartan.TaylorWronskianGrowth
import ModifiedCartan.EntireCountGrowth
import ModifiedCartan.EntireTaylorJets
import FewInflection.FundamentalAnalytic

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_wronskian_differentiable {n : ℕ} {y : Fin (n + 1) → ℂ → ℂ}
    (hy : ∀ j, Differentiable ℂ (y j)) : Differentiable ℂ (FewInflection.wronskian n y) :=
  fun z => (FewInflection.analyticAt_wronskian (fun j => (hy j).analyticAt z)).differentiableAt

/-- The reciprocal-root summability assertion of LaTeX
`lem:entire-majorant`, with all its growth hypotheses proved from the
component orders. This is only the first assertion, not the product majorant. -/
theorem normalized_entire_system_reciprocal_roots {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    (horder : ∀ j, entireOrder (y j) < 1)
    (hjets : ∀ i j : Fin (n + 1), iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0) :
    Summable (fun a : entireZeroCopies (FewInflection.wronskian n y) => ‖a.1‖⁻¹) ∧
      ∃ σ C : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < C ∧ ∀ R, 1 ≤ R →
        (∑' a : entireZeroCopies (FewInflection.wronskian n y),
          if R < ‖a.1‖ then ‖a.1‖⁻¹ else 0) ≤ C * R ^ (σ - 1) := by
  obtain ⟨σ, hσ0, hσ1, hσ⟩ := finite_entireOrder_exists_exponent_lt_one horder
  obtain ⟨D, hD, hb⟩ := entire_wronskian_posLog_bound hy hσ0.le hσ
  have hW := entire_wronskian_differentiable hy
  have hW0 := wronskian_zero_of_initial_jets hjets
  obtain ⟨C, hC, hc⟩ := entire_zeroCount_power_bound hW hW0 hD hb
  refine ⟨entire_reciprocal_roots_summable_of_count_bound hW hC.le hσ1 hc,
    σ, C / (1 - σ), hσ0, hσ1, div_pos hC (sub_pos.mpr hσ1), ?_⟩
  intro R hR
  exact (entire_reciprocal_tail_of_count_bound hW hC.le hσ1 hR hc).2

/-- The uniform escape-of-roots estimate `eq:reciprocal-tail` for every
Taylor Wronskian. Lean's truncation index counts terms, so N>n preserves
all n+1 initial derivatives. -/
theorem taylorWronskian_reciprocal_tail_uniform {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    (horder : ∀ j, entireOrder (y j) < 1)
    (hjets : ∀ i j : Fin (n + 1), iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0) :
    ∃ σ C : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < C ∧ ∀ N, n < N → ∀ R, 1 ≤ R →
      (∑' a : entireZeroCopies (FewInflection.wronskian n
        (fun j z => (FewInflection.taylorPolynomial (y j) 0 N).eval z)),
        if R < ‖a.1‖ then ‖a.1‖⁻¹ else 0) ≤ C * R ^ (σ - 1) := by
  obtain ⟨σ, hσ0, hσ1, hσ⟩ := finite_entireOrder_exists_exponent_lt_one horder
  obtain ⟨D, hD, hb⟩ := entire_taylorWronskian_posLog_bound hy hσ0.le hσ
  let C : ℝ := D * (2 : ℝ) ^ σ / Real.log 2
  have hC : 0 < C := div_pos (mul_pos hD (Real.rpow_pos_of_pos (by norm_num) _))
    (Real.log_pos (by norm_num))
  refine ⟨σ, C / (1 - σ), hσ0, hσ1, div_pos hC (sub_pos.mpr hσ1), ?_⟩
  intro N hN R hR
  have hW := entire_wronskian_differentiable (fun j =>
    (FewInflection.taylorPolynomial (y j) 0 N).differentiable)
  have hW0 := entire_taylorPolynomial_wronskian_zero hN hjets
  have hc : ∀ t, 1 ≤ t → zeroCount
      (FewInflection.wronskian n (fun j z => (FewInflection.taylorPolynomial (y j) 0 N).eval z)) t ≤
      C * t ^ σ := by
    intro t ht
    exact zeroCount_le_of_posLog_bound hW hW0 hD.le ht (hb N (2 * t) (by linarith))
  exact (entire_reciprocal_tail_of_count_bound hW hC.le hσ1 hR hc).2

end ModifiedCartan
#print axioms ModifiedCartan.normalized_entire_system_reciprocal_roots
#print axioms ModifiedCartan.taylorWronskian_reciprocal_tail_uniform

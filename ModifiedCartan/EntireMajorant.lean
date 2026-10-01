import ModifiedCartan.PolynomialIntegralMajorant
import ModifiedCartan.WronskianCountingIntegralLimit
import ModifiedCartan.RootConvolution

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_component_integral_majorant {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    (horder : ∀ j, entireOrder (y j) < 1)
    (hjets : ∀ i j : Fin (n + 1), iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0)
    (j : Fin (n + 1)) {z : ℂ} (hz : z ≠ 0) :
    ‖y j z‖ ≤ (‖z‖ ^ j.val / (j.val.factorial : ℝ)) *
      Real.exp (‖z‖ * ∫ t in Ioi 0, ValueDistribution.logCounting
        (FewInflection.wronskian n y) (0 : WithTop ℂ) t / (‖z‖ + t) ^ 2) := by
  have ht := FewInflection.tendstoLocallyUniformlyOn_taylorPolynomial_eval_of_entire (hy j) 0
  have hl := (ht.tendsto_at (mem_univ z)).norm
  have hi := taylorWronskian_counting_integral_tendsto hy horder hjets (norm_pos_iff.mpr hz)
  have hr := (Real.continuous_exp.continuousAt.tendsto.comp (hi.const_mul ‖z‖)).const_mul
    (‖z‖ ^ j.val / (j.val.factorial : ℝ))
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_gt_atTop n] with N hN
  apply normalized_polynomial_tuple_integral_majorant
    (fun j => FewInflection.taylorPolynomial (y j) 0 N) _ j hz
  intro i k
  rw [entire_taylorPolynomial_iteratedDeriv_zero (y k) (by have := i.isLt; omega)]
  exact hjets i k

namespace Paper

/-- LaTeX `lem:entire-majorant`, equation `eq:entire-majorant`.
The index is the actual zero divisor, repeated with analytic multiplicity.
The limiting step uses Jensen counting integrals and dominated convergence;
this alternative to individual root matching is recorded in the map. -/
theorem lem_entire_majorant {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    (horder : ∀ j, entireOrder (y j) < 1)
    (hjets : ∀ i j : Fin (n + 1), iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0) :
    Summable (fun a : entireZeroCopies (FewInflection.wronskian n y) => ‖a.1‖⁻¹) ∧
      ∀ (j : Fin (n + 1)) (z : ℂ),
        ‖y j z‖ ≤ (‖z‖ ^ j.val / (j.val.factorial : ℝ)) *
          rootMajorantProduct (FewInflection.wronskian n y) ‖z‖ := by
  classical
  have hs := (normalized_entire_system_reciprocal_roots hy horder hjets).1
  refine ⟨hs, ?_⟩
  intro j z
  by_cases hz : z = 0
  · subst z
    have hj0 : y j 0 = if (0 : Fin (n + 1)) = j then 1 else 0 := by
      simpa only [iteratedDeriv_zero, Fin.val_zero] using hjets 0 j
    by_cases hj : j = 0
    · subst j
      simp [hj0, rootMajorantProduct]
    · have hv : j.val ≠ 0 := fun hv => hj (Fin.ext hv)
      simp [hj0, hj, Ne.symm hj, hv, rootMajorantProduct]
  · have hb := entire_component_integral_majorant hy horder hjets j hz
    have he := (normalized_wronskian_product_convolution hy horder hjets (norm_pos_iff.mpr hz)).2
    rw [← he, Real.exp_log (rootMajorantProduct_pos hs (norm_nonneg z))] at hb
    exact hb

end Paper
end ModifiedCartan
#print axioms ModifiedCartan.entire_component_integral_majorant
#print axioms ModifiedCartan.Paper.lem_entire_majorant

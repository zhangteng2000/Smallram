import ModifiedCartan.PolynomialNegativeArea
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.JensenFormula

open scoped Topology BigOperators Classical
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem circleAverage_le_of_codiscrete_le {v : ℂ → ℝ} {c : ℂ} {R M : ℝ}
    (hR : R ≠ 0) (hv : CircleIntegrable v c R)
    (hM : ∀ᶠ z in codiscreteWithin (sphere c |R|), v z ≤ M) :
    Real.circleAverage v c R ≤ M := by
  let w : ℂ → ℝ := fun z => min (v z) M
  have heq : v =ᶠ[codiscreteWithin (sphere c |R|)] w := by
    filter_upwards [hM] with z hz
    exact (min_eq_left hz).symm
  rw [Real.circleAverage_congr_codiscreteWithin heq hR]
  exact Real.circleAverage_mono_on_of_le_circle
    (CircleIntegrable.congr_codiscreteWithin heq hv) (fun z _ => min_le_right (v z) M)

theorem circleAverage_log_norm_monic_nonneg (P : Polynomial ℂ) (hP : P.Monic)
    (c : ℂ) : 0 ≤ Real.circleAverage (fun z => Real.log ‖P.eval z‖) c 1 := by
  obtain ⟨a, ha⟩ := monic_polynomial_eval_root_product P hP
  have hnonzero : ∀ᶠ z in codiscreteWithin (sphere c |(1 : ℝ)|),
      ∀ i, z - a i ≠ 0 := by
    filter_upwards [compl_finite_mem_codiscreteWithin (Set.finite_range a)] with z hz i
    exact sub_ne_zero.mpr (fun hi => hz ⟨i, hi.symm⟩)
  have heq : (fun z => Real.log ‖P.eval z‖) =ᶠ[codiscreteWithin (sphere c |(1 : ℝ)|)]
      (fun z => ∑ i, Real.log ‖z - a i‖) := by
    filter_upwards [hnonzero] with z hz
    rw [ha, norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (hz i))]
  rw [Real.circleAverage_congr_codiscreteWithin heq (by norm_num)]
  have hint (i : Fin P.natDegree) : CircleIntegrable (fun z => Real.log ‖z - a i‖) c 1 :=
    (show MeromorphicOn (fun z : ℂ => z - a i) (sphere c |(1 : ℝ)|) by
      intro z _; fun_prop).circleIntegrable_log_norm
  rw [Real.circleAverage_fun_sum (fun i _ => hint i)]
  apply Finset.sum_nonneg
  intro i _
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (by norm_num : (1 : ℝ) ≠ 0)]
  simp only [Real.log_one, zero_add]
  exact Real.posLog_nonneg

/-- A monic factor cannot hide a large analytic exponential factor on a unit
disk. Auxiliary alternative proof of the norm bound in `prop:representation`. -/
theorem analytic_exp_factor_re_le_log_bound (P : Polynomial ℂ) (hP : P.Monic)
    {A : ℂ → ℂ} {c : ℂ} (hA : AnalyticOnNhd ℂ A (closedBall c 1))
    {M : ℝ} (_hM : 0 < M)
    (hbound : ∀ z ∈ sphere c 1, ‖P.eval z * Complex.exp (A z)‖ ≤ M) :
    (A c).re ≤ Real.log M := by
  have hPint : CircleIntegrable (fun z => Real.log ‖P.eval z‖) c 1 :=
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr P.differentiable).meromorphicOn.mono_set
      (subset_univ (sphere c |(1 : ℝ)|))).circleIntegrable_log_norm
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => (A z).re) (closedBall c |(1 : ℝ)|) := by
    simpa using (show InnerProductSpace.HarmonicOnNhd (fun z => (A z).re) (closedBall c 1) from
      fun z hz => (hA z hz).harmonicAt_re)
  have hAint : CircleIntegrable (fun z => (A z).re) c 1 :=
    (hharm.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  have hnonzero : ∀ᶠ z in codiscreteWithin (sphere c |(1 : ℝ)|), P.eval z ≠ 0 := by
    exact compl_finite_mem_codiscreteWithin (Polynomial.finite_setOfPred_isRoot hP.ne_zero)
  have hle := circleAverage_le_of_codiscrete_le (by norm_num : (1 : ℝ) ≠ 0)
    (hPint.add hAint) (by
      filter_upwards [hnonzero, self_mem_codiscreteWithin (sphere c |(1 : ℝ)|)] with z hz hzin
      have hprod : P.eval z * Complex.exp (A z) ≠ 0 := mul_ne_zero hz (Complex.exp_ne_zero _)
      have hlog := Real.log_le_log (norm_pos_iff.mpr hprod) (hbound z (by simpa using hzin))
      rw [norm_mul, Complex.norm_exp,
        Real.log_mul (norm_ne_zero_iff.mpr hz) (Real.exp_ne_zero _), Real.log_exp] at hlog
      exact hlog)
  rw [Real.circleAverage_add hPint hAint, hharm.circleAverage_eq] at hle
  linarith [circleAverage_log_norm_monic_nonneg P hP c]

end
end ModifiedCartan
#print axioms ModifiedCartan.analytic_exp_factor_re_le_log_bound

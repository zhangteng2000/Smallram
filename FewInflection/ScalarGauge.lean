import FewInflection.Gauge
import FewInflection.Jensen

open scoped BigOperators Topology
open Filter MeromorphicAt MeromorphicOn MeasureTheory Metric Real Set Topology

namespace FewInflection

noncomputable section

theorem scalar_circleAverage_log_norm_eq_center_of_nonvanishing
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgnz : ∀ z, g z ≠ 0) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun z : ℂ => Real.log ‖g z‖) 0 r =
      Real.log ‖g 0‖ := by
  have hA : AnalyticOnNhd ℂ g Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  have hdiv : MeromorphicOn.divisor g Set.univ = 0 := by
    ext z
    rw [hA.divisor_apply (Set.mem_univ z)]
    simp [(hA z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr (hgnz z)]
  have hcount : ValueDistribution.logCounting g (0 : WithTop ℂ) r = 0 := by
    rw [ValueDistribution.logCounting_zero, hdiv]
    simp
  have hJ := logCounting_zero_eq_circleAverage_sub_const_of_entire
    hg hr (hgnz 0)
  linarith

theorem characteristic_scalarGauge_eventuallyEq
    {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g) :
    characteristic (f.scalarGauge g hg hgd) =ᶠ[atTop] characteristic f := by
  have hvec_cont : Continuous (fun z : ℂ => ‖f.vector z‖) := by
    exact (continuous_pi (fun j => (f.holomorphic j).continuous)).norm
  have hlog_cont : Continuous (fun z : ℂ => Real.log ‖f.vector z‖) := by
    apply hvec_cont.log
    intro z
    exact norm_ne_zero_iff.mpr (f.vector_ne_zero z)
  have hscalar_cont : Continuous (fun z : ℂ => Real.log ‖g z‖) := by
    apply (hgd.continuous.norm).log
    intro z
    exact norm_ne_zero_iff.mpr (hg z)
  have hsum_int (r : ℝ) : CircleIntegrable
      (fun z : ℂ => Real.log ‖g z‖ + Real.log ‖f.vector z‖) 0 r := by
    exact (hscalar_cont.add hlog_cont).continuousOn.circleIntegrable'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have havg : Real.circleAverage
      (fun z : ℂ => Real.log ‖g z‖ + Real.log ‖f.vector z‖) 0 r =
      Real.log ‖g 0‖ +
        Real.circleAverage (fun z : ℂ => Real.log ‖f.vector z‖) 0 r := by
    rw [Real.circleAverage_fun_add (hscalar_cont.continuousOn.circleIntegrable')
      (hlog_cont.continuousOn.circleIntegrable')]
    rw [scalar_circleAverage_log_norm_eq_center_of_nonvanishing hgd hg hr]
  have hlogmul (z : ℂ) :
      Real.log ‖(f.scalarGauge g hg hgd).vector z‖ =
        Real.log ‖g z‖ + Real.log ‖f.vector z‖ := by
    rw [Curve.scalarGauge_vector, norm_smul,
      Real.log_mul (norm_ne_zero_iff.mpr (hg z))
        (norm_ne_zero_iff.mpr (f.vector_ne_zero z))]
  have hzero := hlogmul 0
  unfold characteristic
  rw [show (fun z : ℂ => Real.log ‖(f.scalarGauge g hg hgd).vector z‖) =
      (fun z : ℂ => Real.log ‖g z‖ + Real.log ‖f.vector z‖) by
        funext z; exact hlogmul z]
  rw [havg, hzero]
  ring

/-- A nowhere-zero entire scalar gauge does not change whether a curve has a
polynomial representation. -/
theorem Curve.scalarGauge_transcendental_iff
    {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g) :
    f.Transcendental ↔
      (f.scalarGauge g hg hgd).Transcendental := by
  constructor
  · intro htrans hrep
    apply htrans
    rcases hrep with ⟨p, h, hh, hhd, hrep⟩
    refine ⟨p, fun z => h z / g z, ?_, ?_, ?_⟩
    · intro z
      exact div_ne_zero (hh z) (hg z)
    · exact hhd.div hgd hg
    · intro j z
      have heq := hrep j z
      change g z * f.coord j z = h z * (p j).eval z at heq
      change f.coord j z = (h z / g z) * (p j).eval z
      field_simp [hg z]
      simpa [mul_comm, mul_left_comm, mul_assoc] using heq
  · intro htrans hrep
    apply htrans
    rcases hrep with ⟨p, h, hh, hhd, hrep⟩
    refine ⟨p, fun z => g z * h z, ?_, ?_, ?_⟩
    · intro z
      exact mul_ne_zero (hg z) (hh z)
    · exact hgd.mul hhd
    · intro j z
      have heq := hrep j z
      change g z * f.coord j z = (g z * h z) * (p j).eval z
      rw [heq]
      ring

/-- A nowhere-zero scalar gauge also preserves linear nondegeneracy. -/
theorem Curve.scalarGauge_linearlyNonDegenerate_iff
    {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g) :
    f.linearlyNonDegenerate ↔
      (f.scalarGauge g hg hgd).linearlyNonDegenerate := by
  constructor
  · intro hlin
    unfold Curve.linearlyNonDegenerate at hlin ⊢
    rw [Fintype.linearIndependent_iff] at hlin ⊢
    intro c hc j
    have hzero : (∑ i : Index n, c i • f.coord i) = 0 := by
      funext z
      have hcz : ∑ i : Index n, c i • (g z * f.coord i z) = 0 := by
        simpa [Curve.scalarGauge, Finset.sum_apply, smul_eq_mul] using congrFun hc z
      have hfactor :
          (∑ i : Index n, c i • (g z * f.coord i z)) =
            g z * (∑ i : Index n, c i • f.coord i z) := by
        simp [smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      rw [hfactor] at hcz
      have hzsum := (mul_eq_zero.mp hcz).resolve_left (hg z)
      simpa [Finset.sum_apply, smul_eq_mul] using hzsum
    exact hlin c hzero j
  · intro hlin
    unfold Curve.linearlyNonDegenerate at hlin ⊢
    rw [Fintype.linearIndependent_iff] at hlin ⊢
    intro c hc j
    have hzeroGauge :
        (∑ i : Index n, c i • (f.scalarGauge g hg hgd).coord i) = 0 := by
      funext z
      simp only [Finset.sum_apply, Pi.zero_apply]
      change ∑ i : Index n, c i • (g z * f.coord i z) = 0
      have hcz : ∑ i : Index n, c i • f.coord i z = 0 := by
        simpa [Finset.sum_apply, smul_eq_mul] using congrFun hc z
      have hfactor :
          (∑ i : Index n, c i • (g z * f.coord i z)) =
            g z * (∑ i : Index n, c i • f.coord i z) := by
        simp [smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      rw [hfactor, hcz, mul_zero]
    exact hlin c hzeroGauge j

/-- A nowhere-zero entire scalar gauge preserves both projective growth orders.
The proof uses the eventual characteristic identity and the congruence
lemmas for filter limsup and liminf. -/
theorem Curve.scalarGauge_order_lowerOrder_eq
    {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g) :
    order (f.scalarGauge g hg hgd) = order f ∧
      lowerOrder (f.scalarGauge g hg hgd) = lowerOrder f := by
  have hchar := characteristic_scalarGauge_eventuallyEq f g hg hgd
  have hratio :
      logGrowthRatio (f.scalarGauge g hg hgd) =ᶠ[atTop]
        logGrowthRatio f := by
    filter_upwards [hchar] with r hr
    simp only [logGrowthRatio, hr]
  constructor
  · unfold order
    exact limsup_congr hratio
  · unfold lowerOrder
    exact liminf_congr hratio

end

end FewInflection

import ModifiedCartan.ZeroCopyLogCounting
import ModifiedCartan.EnvelopeKernel

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_logCounting_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) {t : ℝ} (ht : 0 < t) :
    0 ≤ ValueDistribution.logCounting f (0 : WithTop ℂ) t := by
  rw [entire_logCounting_eq_tsum_zeroCopies hf h0 ht]
  exact tsum_nonneg (fun _ => Real.posLog_nonneg)

theorem entire_logCounting_aestronglyMeasurableOn {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    AEStronglyMeasurable (ValueDistribution.logCounting f (0 : WithTop ℂ))
      (volume.restrict (Ioi (0 : ℝ))) := by
  letI : Countable (entireZeroCopies f) := entireZeroCopies_countable hf
  have hm : Measurable (fun t : ℝ => ∑' a : entireZeroCopies f, Real.posLog (t / ‖a.1‖)) := by
    fun_prop
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (entire_logCounting_eq_tsum_zeroCopies hf h0 ht).symm

theorem logCounting_le_of_posLog_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 = 1) {r B : ℝ} (hr : 0 < r)
    (hb : ∀ z ∈ sphere (0 : ℂ) r, Real.posLog ‖f z‖ ≤ B) :
    ValueDistribution.logCounting f (0 : WithTop ℂ) r ≤ B := by
  rw [FewInflection.logCounting_zero_eq_circleAverage_sub_const_of_entire hf hr
    (by rw [h0]; exact one_ne_zero), h0, norm_one, Real.log_one, sub_zero]
  have hi : CircleIntegrable (fun z => Real.log ‖f z‖) 0 r :=
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono
      (subset_univ (sphere 0 |r|))).meromorphicOn.circleIntegrable_log_norm
  apply Real.circleAverage_mono_on_of_le_circle hi
  intro z hz
  exact (le_max_right 0 _).trans (hb z (by simpa only [abs_of_pos hr] using hz))

theorem logCounting_le_power_envelope {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 = 1) {D σ : ℝ} (hD : 0 ≤ D)
    (hb : ∀ r, 1 ≤ r → ∀ z ∈ closedBall (0 : ℂ) r, Real.posLog ‖f z‖ ≤ D * r ^ σ)
    {t : ℝ} (ht : 0 < t) :
    ValueDistribution.logCounting f (0 : WithTop ℂ) t ≤ D * max 1 (t ^ σ) := by
  by_cases ht1 : 1 ≤ t
  · exact (logCounting_le_of_posLog_bound hf h0 ht
      (fun z hz => hb t ht1 z (sphere_subset_closedBall hz))).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hD)
  · have hmono : ValueDistribution.logCounting f (0 : WithTop ℂ) t ≤
        ValueDistribution.logCounting f (0 : WithTop ℂ) 1 :=
      ValueDistribution.logCounting_monotoneOn ht (by norm_num) (le_of_not_ge ht1)
    have h1 := logCounting_le_of_posLog_bound hf h0 zero_lt_one
      (fun z hz => hb 1 le_rfl z (sphere_subset_closedBall hz))
    simp only [Real.one_rpow, mul_one] at h1
    have hbound : D ≤ D * max 1 (t ^ σ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (le_max_left 1 (t ^ σ)) hD
    exact (hmono.trans h1).trans hbound

set_option maxHeartbeats 800000 in
/-- Integrable majorant for the counting kernels in Step 3 of
LaTeX `lem:entire-majorant`. -/
theorem power_counting_kernel_integrable {σ r : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => max 1 (t ^ σ) / (r + t) ^ 2) (Ioi 0) := by
  have hc : ContinuousOn (fun t : ℝ => max 1 (t ^ σ) / (r + t) ^ 2) (Ici 0) := by
    apply (continuous_const.max (Real.continuous_rpow_const hσ)).continuousOn.div (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (by change 0 ≤ t at ht; linarith)
  have hhead : IntegrableOn (fun t : ℝ => max 1 (t ^ σ) / (r + t) ^ 2) (Ioc 0 1) :=
    ((hc.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have htail : IntegrableOn (fun t : ℝ => max 1 (t ^ σ) / (r + t) ^ 2) (Ioi 1) := by
    have hp : IntegrableOn (fun t : ℝ => t ^ (σ - 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : σ - 2 < -1) zero_lt_one
    have hm : AEStronglyMeasurable
        (fun t : ℝ => max 1 (t ^ σ) / (r + t) ^ 2) (volume.restrict (Ioi (1 : ℝ))) :=
      (hc.mono (fun t (ht : (1 : ℝ) < t) => (zero_lt_one.trans ht).le)).aestronglyMeasurable measurableSet_Ioi
    apply hp.mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_of_nonneg (div_nonneg (zero_le_one.trans (le_max_left _ _)) (sq_nonneg _)),
      max_eq_right (Real.one_le_rpow ht.le hσ), Real.rpow_sub ht0, Real.rpow_two]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg ht0.le _) (sq_pos_of_pos ht0)
    nlinarith
  simpa only [Ioc_union_Ioi_eq_Ioi zero_le_one] using hhead.union htail

end ModifiedCartan
#print axioms ModifiedCartan.logCounting_le_power_envelope
#print axioms ModifiedCartan.power_counting_kernel_integrable

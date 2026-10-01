import ModifiedCartan.CauchyKernel
import Mathlib.Analysis.Analytic.IsolatedZeros

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Logarithmic kernels and local integrability needed in `lem:logderivlimit`.
The full convergence theorem remains a separate proof obligation. -/

theorem norm_log_norm_sub_le (z a : ℂ) :
    ‖Real.log ‖z - a‖‖ ≤ ‖z - a‖ + ‖(z - a)⁻¹‖ := by
  rw [Real.norm_eq_abs, norm_inv]
  apply abs_le.mpr
  have h := norm_nonneg (z - a)
  constructor
  · linarith [Real.neg_inv_le_log h]
  · linarith [Real.log_le_self h, inv_nonneg.mpr h]

theorem integrableOn_logKernel (a : ℂ) {K : Set ℂ} (hK : IsCompact K) :
    IntegrableOn (fun z : ℂ => Real.log ‖z - a‖) K := by
  have hn : IntegrableOn (fun z : ℂ => ‖z - a‖) K :=
    (continuous_id.sub continuous_const).norm.continuousOn.integrableOn_compact hK
  have hi : IntegrableOn (fun z : ℂ => (z - a)⁻¹) K := by
    apply memLp_one_iff_integrable.mp
    simpa only [ENNReal.ofReal_one] using
      memLp_cauchyKernel_on_compact (p := 1) zero_lt_one (by norm_num) a hK
  have hmeas : AEStronglyMeasurable (fun z : ℂ => Real.log ‖z - a‖) (volume.restrict K) :=
    (Real.measurable_log.comp (measurable_id.sub measurable_const).norm).aestronglyMeasurable
  exact (hn.add hi.norm).mono' hmeas (Filter.Eventually.of_forall (fun z => norm_log_norm_sub_le z a))

theorem locallyIntegrable_logKernel (a : ℂ) :
    LocallyIntegrable (fun z : ℂ => Real.log ‖z - a‖) := by
  rw [locallyIntegrable_iff]
  exact fun K hK => integrableOn_logKernel a hK

theorem integrableAt_log_norm_of_analyticAt {H : ℂ → ℂ} {a : ℂ}
    (hH : AnalyticAt ℂ H a) :
    IntegrableAtFilter (fun z => Real.log ‖H z‖) (𝓝 a) volume := by
  by_cases hzero : ∀ᶠ z in 𝓝 a, H z = 0
  · obtain ⟨r, hr, heq⟩ := Metric.eventually_nhds_iff_ball.mp hzero
    refine ⟨ball a r, ball_mem_nhds a hr, ?_⟩
    apply integrableOn_zero.congr_fun _ measurableSet_ball
    intro z hz
    simp [heq z hz]
  · obtain ⟨n, g, hg, hg0, heq⟩ := hH.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hzero
    have hevent : ∀ᶠ z in 𝓝 a,
        H z = (z - a) ^ n * g z ∧ AnalyticAt ℂ g z ∧ g z ≠ 0 := by
      filter_upwards [heq, hg.eventually_analyticAt, hg.continuousAt.eventually_ne hg0]
        with z hz hz_an hz0
      exact ⟨by simpa only [smul_eq_mul] using hz, hz_an, hz0⟩
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevent
    let K := closedBall a (r / 2)
    have hK : IsCompact K := isCompact_closedBall a (r / 2)
    have hsub : K ⊆ ball a r := closedBall_subset_ball (half_lt_self hr)
    have hgc : ContinuousOn (fun z => Real.log ‖g z‖) K := by
      intro z hz
      exact ((hball z (hsub hz)).2.1.continuousAt.norm.log
        (norm_ne_zero_iff.mpr (hball z (hsub hz)).2.2)).continuousWithinAt
    have hint : IntegrableOn (fun z => (n : ℝ) * Real.log ‖z - a‖ + Real.log ‖g z‖) K :=
      ((integrableOn_logKernel a hK).const_mul (n : ℝ)).add (hgc.integrableOn_compact hK)
    refine ⟨K, closedBall_mem_nhds a (half_pos hr), hint.congr ?_⟩
    filter_upwards [ae_restrict_mem hK.measurableSet,
      ae_restrict_of_ae (volume.ae_ne a)] with z hz hza
    have hzinfo := hball z (hsub hz)
    rw [hzinfo.1, norm_mul, norm_pow,
      Real.log_mul (pow_ne_zero n (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza)))
        (norm_ne_zero_iff.mpr hzinfo.2.2), Real.log_pow]

theorem locallyIntegrableOn_log_norm {H : ℂ → ℂ} {U : Set ℂ}
    (hH : AnalyticOnNhd ℂ H U) :
    LocallyIntegrableOn (fun z => Real.log ‖H z‖) U := by
  intro z hz
  exact (integrableAt_log_norm_of_analyticAt (hH z hz)).filter_mono nhdsWithin_le_nhds

theorem integrableOn_log_norm_on_compact {H : ℂ → ℂ} {U K : Set ℂ}
    (hH : AnalyticOnNhd ℂ H U) (hKU : K ⊆ U) (hK : IsCompact K) :
    IntegrableOn (fun z => Real.log ‖H z‖) K :=
  (locallyIntegrableOn_log_norm hH).integrableOn_compact_subset hKU hK

end ModifiedCartan



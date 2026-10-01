import ModifiedCartan.LogLp

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Every finite positive Lp exponent is allowed for the log modulus of an
analytic function. Supporting membership result for `lem:logderivlimit`.
No assertion about subharmonic representatives at zeros is made here. -/

theorem exists_closedBall_memLp_log_norm {H : ℂ → ℂ} {a : ℂ} {p : ℝ}
    (hH : AnalyticAt ℂ H a) (hp : 0 < p) :
    ∃ r : ℝ, 0 < r ∧ MemLp (fun z => Real.log ‖H z‖) (ENNReal.ofReal p)
      (volume.restrict (closedBall a r)) := by
  by_cases hzero : ∀ᶠ z in 𝓝 a, H z = 0
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hzero
    refine ⟨r / 2, half_pos hr, ?_⟩
    apply (memLp_congr_ae (f := (0 : ℂ → ℝ)) ?_).mp MemLp.zero
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    simp only [hball z (closedBall_subset_ball (half_lt_self hr) hz), norm_zero, Real.log_zero]
    rfl
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
    have hgm : MemLp (fun z => Real.log ‖g z‖) (ENNReal.ofReal p) (volume.restrict K) := by
      apply (integrable_norm_rpow_iff (hgc.aestronglyMeasurable hK.measurableSet)
        (by simpa using hp) ENNReal.ofReal_ne_top).mp
      exact (hgc.norm.rpow_const (fun _ _ => Or.inr ENNReal.toReal_nonneg)).integrableOn_compact hK
    have hint : MemLp ((fun z : ℂ => (n : ℝ) * Real.log ‖z - a‖) +
        (fun z => Real.log ‖g z‖)) (ENNReal.ofReal p) (volume.restrict K) :=
      ((memLp_logKernel_on_compact hp a hK).const_smul (n : ℝ)).add hgm
    refine ⟨r / 2, half_pos hr, ?_⟩
    apply (memLp_congr_ae (f := (fun z : ℂ => (n : ℝ) * Real.log ‖z - a‖) +
      (fun z => Real.log ‖g z‖)) ?_).mp hint
    filter_upwards [ae_restrict_mem hK.measurableSet,
      ae_restrict_of_ae (volume.ae_ne a)] with z hz hza
    have hzinfo := hball z (hsub hz)
    rw [hzinfo.1, norm_mul, norm_pow,
      Real.log_mul (pow_ne_zero n (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza)))
        (norm_ne_zero_iff.mpr hzinfo.2.2), Real.log_pow]
    rfl

theorem memLp_log_norm_on_compact {H : ℂ → ℂ} {U K : Set ℂ} {p : ℝ}
    (hH : AnalyticOnNhd ℂ H U) (hKU : K ⊆ U) (hK : IsCompact K) (hp : 0 < p) :
    MemLp (fun z => Real.log ‖H z‖) (ENNReal.ofReal p) (volume.restrict K) := by
  have hmeas := (integrableOn_log_norm_on_compact hH hKU hK).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hmeas (by simpa using hp) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hp.le]
  have hlocal : LocallyIntegrableOn (fun z => ‖Real.log ‖H z‖‖ ^ p) U := by
    intro z hz
    obtain ⟨r, hr, hint⟩ := exists_closedBall_memLp_log_norm (hH z hz) hp
    have hi : IntegrableOn (fun z => ‖Real.log ‖H z‖‖ ^ p) (closedBall z r) := by
      simpa only [IntegrableOn, ENNReal.toReal_ofReal hp.le] using
        hint.integrable_norm_rpow (by simpa using hp) ENNReal.ofReal_ne_top
    exact (show IntegrableAtFilter (fun z => ‖Real.log ‖H z‖‖ ^ p) (𝓝 z) volume from
      ⟨closedBall z r, closedBall_mem_nhds z hr, hi⟩).filter_mono nhdsWithin_le_nhds
  exact hlocal.integrableOn_compact_subset hKU hK

end ModifiedCartan



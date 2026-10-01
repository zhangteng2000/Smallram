import ModifiedCartan.LogKernel

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Local Lp membership of the logarithmic derivative, needed in
`lem:logderivlimit`. This file proves membership, not the convergence assertion.
Values at isolated zeros are handled by almost-everywhere equality. -/

theorem memLp_of_continuousOn_compact {F : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hF : ContinuousOn F K) (p : ℝ≥0∞) :
    MemLp F p (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  apply MemLp.of_bound (hF.aestronglyMeasurable hK.measurableSet) C
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact hC z hz

theorem exists_closedBall_memLp_logDeriv {H : ℂ → ℂ} {a : ℂ} {p : ℝ}
    (hH : AnalyticAt ℂ H a) (hp0 : 0 < p) (hp2 : p < 2) :
    ∃ r : ℝ, 0 < r ∧ MemLp (logDeriv H) (ENNReal.ofReal p)
      (volume.restrict (closedBall a r)) := by
  by_cases hzero : ∀ᶠ z in 𝓝 a, H z = 0
  · have hld : ∀ᶠ z in 𝓝 a, logDeriv H z = 0 := by
      filter_upwards [logDeriv_congr_nhds hzero] with z hz
      simpa only [logDeriv_const, Pi.zero_apply] using hz
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hld
    refine ⟨r / 2, half_pos hr, ?_⟩
    apply (memLp_congr_ae (f := (0 : ℂ → ℂ)) ?_).mp MemLp.zero
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact (hball z (closedBall_subset_ball (half_lt_self hr) hz)).symm
  · obtain ⟨n, g, hg, hg0, heq⟩ := hH.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hzero
    have heq' : H =ᶠ[𝓝 a] (fun z => (z - a) ^ n * g z) := by
      filter_upwards [heq] with z hz
      simpa only [smul_eq_mul] using hz
    have hevent : ∀ᶠ z in 𝓝 a,
        logDeriv H z = logDeriv (fun w => (w - a) ^ n * g w) z ∧
          AnalyticAt ℂ g z ∧ g z ≠ 0 := by
      exact (logDeriv_congr_nhds heq').and
        (hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hg0))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevent
    let K := closedBall a (r / 2)
    have hK : IsCompact K := isCompact_closedBall a (r / 2)
    have hsub : K ⊆ ball a r := closedBall_subset_ball (half_lt_self hr)
    have hgc : ContinuousOn (logDeriv g) K := by
      intro z hz
      have hinfo := hball z (hsub hz)
      exact (hinfo.2.1.deriv.continuousAt.div hinfo.2.1.continuousAt hinfo.2.2).continuousWithinAt
    have hint : MemLp ((fun z : ℂ => (n : ℂ) * (z - a)⁻¹) + logDeriv g)
        (ENNReal.ofReal p) (volume.restrict K) := by
      have hpole := (memLp_cauchyKernel_on_compact hp0 hp2 a hK).const_smul (n : ℂ)
      exact hpole.add (memLp_of_continuousOn_compact hK hgc _)
    refine ⟨r / 2, half_pos hr, ?_⟩
    apply (memLp_congr_ae (f := (fun z : ℂ => (n : ℂ) * (z - a)⁻¹) + logDeriv g) ?_).mp hint
    filter_upwards [ae_restrict_mem hK.measurableSet,
      ae_restrict_of_ae (volume.ae_ne a)] with z hz hza
    have hinfo := hball z (hsub hz)
    have hshift : logDeriv (fun w : ℂ => w - a) z = (z - a)⁻¹ := by
      have hd : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
      rw [logDeriv_apply, hd.deriv, one_div]
    symm
    rw [hinfo.1, logDeriv_mul (f := fun w : ℂ => (w - a) ^ n) (g := g)
      z (pow_ne_zero n (sub_ne_zero.mpr hza)) hinfo.2.2
      (by fun_prop) hinfo.2.1.differentiableAt,
      logDeriv_fun_pow (f := fun w : ℂ => w - a) (x := z) (by fun_prop) n, hshift]
    rfl

theorem locallyIntegrableOn_logDeriv {H : ℂ → ℂ} {U : Set ℂ}
    (hH : AnalyticOnNhd ℂ H U) : LocallyIntegrableOn (logDeriv H) U := by
  intro z hz
  obtain ⟨r, hr, hint⟩ := exists_closedBall_memLp_logDeriv (hH z hz)
    (p := 1) zero_lt_one (by norm_num)
  have hi : IntegrableOn (logDeriv H) (closedBall z r) := by
    simpa only [IntegrableOn, ENNReal.ofReal_one, memLp_one_iff_integrable] using hint
  exact (show IntegrableAtFilter (logDeriv H) (𝓝 z) volume from
    ⟨closedBall z r, closedBall_mem_nhds z hr, hi⟩).filter_mono nhdsWithin_le_nhds

theorem memLp_logDeriv_on_compact {H : ℂ → ℂ} {U K : Set ℂ} {p : ℝ}
    (hH : AnalyticOnNhd ℂ H U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hp0 : 0 < p) (hp2 : p < 2) :
    MemLp (logDeriv H) (ENNReal.ofReal p) (volume.restrict K) := by
  have hmeas := ((locallyIntegrableOn_logDeriv hH).integrableOn_compact_subset hKU hK).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hmeas (by simpa using hp0) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hp0.le]
  have hlocal : LocallyIntegrableOn (fun z => ‖logDeriv H z‖ ^ p) U := by
    intro z hz
    obtain ⟨r, hr, hint⟩ := exists_closedBall_memLp_logDeriv (hH z hz) hp0 hp2
    have hi : IntegrableOn (fun z => ‖logDeriv H z‖ ^ p) (closedBall z r) := by
      simpa only [IntegrableOn, ENNReal.toReal_ofReal hp0.le] using
        hint.integrable_norm_rpow (by simpa using hp0) ENNReal.ofReal_ne_top
    exact (show IntegrableAtFilter (fun z => ‖logDeriv H z‖ ^ p) (𝓝 z) volume from
      ⟨closedBall z r, closedBall_mem_nhds z hr, hi⟩).filter_mono nhdsWithin_le_nhds
  exact hlocal.integrableOn_compact_subset hKU hK

end ModifiedCartan



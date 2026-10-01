import ModifiedCartan.PolynomialLogMajorant
import ModifiedCartan.JetLogCompactness
import ModifiedCartan.SubharmonicRepresentative

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The initial-value majorant gives the upper point inequality in
`lem:basis-at-point`, for the genuine subharmonic representative. -/
theorem log_limit_value_le_singular_exponent {n : ℕ} {s σ b : ℕ → ℝ}
    {f : ℕ → ℂ → ℂ} {a : ℂ} {ell D C : ℝ} {u : ℂ → EReal} {v : ℂ → ℝ}
    (ha : a ∈ ball (0 : ℂ) 2) (hD : 0 < D)
    (hspos : ∀ ν, 0 < s ν) (hs : Tendsto s atTop atTop) (hσpos : ∀ ν, 0 < σ ν)
    (hσlim : Tendsto (fun ν => Real.log (σ ν) / s ν) atTop (𝓝 ell))
    (hb : ∀ᶠ ν in atTop, b ν / s ν ≤ C)
    (hmajor : ∀ᶠ ν in atTop, ∀ z ∈ ball a 1,
      ‖f ν z‖ ≤ σ ν * (D * s ν ^ n) * Real.exp (‖z - a‖ * b ν))
    (hu : IsSubharmonicOn (ball (0 : ℂ) 4) u)
    (hrep : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hconv : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (s ν) (f ν)) v) : u a ≤ (ell : EReal) := by
  have hball : ball a 1 ⊆ ball (0 : ℂ) 4 := ball_subset_closedBall.trans (closed_unit_disk_subset_D4 ha)
  obtain ⟨ns, hns, hl⟩ := hconv.normalizedLog_real.exists_seq_tendsto_ae one_ne_zero isOpen_ball
  have hnz : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4), ∀ ν, f ν z ≠ 0 :=
    ae_all_iff.mpr (fun ν => hconv.normalizedLog_ae_ne_zero (hspos ν))
  have hae : ∀ᵐ z ∂volume.restrict (ball a 1), u z ≤ ((ell + ‖z - a‖ * C : ℝ) : EReal) := by
    filter_upwards [hl.filter_mono (ae_mono (Measure.restrict_mono_set _ hball)),
      hnz.filter_mono (ae_mono (Measure.restrict_mono_set _ hball)),
      hrep.filter_mono (ae_mono (Measure.restrict_mono_set _ hball)),
      ae_restrict_mem measurableSet_ball] with z hzlim hznz hzrep hzball
    have hreal : Tendsto (fun ν => Real.log ‖f (ns ν) z‖ / s (ns ν)) atTop (𝓝 (v z)) := by
      simpa only [div_eq_mul_inv, mul_comm] using hzlim
    have hh : v z ≤ ell + ‖z - a‖ * C := by
      apply normalized_log_limit_le_of_polynomial_majorant n hD (norm_nonneg _)
        (fun ν => hspos (ns ν)) (hs.comp hns.tendsto_atTop) (fun ν => hσpos (ns ν))
        (Eventually.of_forall (fun ν => norm_pos_iff.mpr (hznz (ns ν))))
        (hσlim.comp hns.tendsto_atTop) hreal (hns.tendsto_atTop.eventually hb)
      filter_upwards [hns.tendsto_atTop.eventually hmajor] with ν hν
      exact hν z hzball
    rw [hzrep]
    exact EReal.coe_le_coe_iff.mpr hh
  have hc : Continuous (fun z : ℂ => ((ell + ‖z - a‖ * C : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (by fun_prop)
  have hp := (hu.mono hball).le_of_ae_le_upperSemicontinuous
    hc.continuousOn.upperSemicontinuousOn isOpen_ball hae a (mem_ball_self zero_lt_one)
  simpa only [sub_self, norm_zero, zero_mul, add_zero] using hp

end ModifiedCartan
#print axioms ModifiedCartan.log_limit_value_le_singular_exponent

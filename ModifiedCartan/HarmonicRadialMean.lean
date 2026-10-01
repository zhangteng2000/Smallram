import ModifiedCartan.HarmonicWeak
import Mathlib.Analysis.Complex.Harmonic.MeanValue

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! Radial weighted mean values for the harmonic interior estimates used in
`lem:logderivlimit`. The proof derives the planar formula from the proved
circle mean theorem by polar integration. No continuity outside the harmonic
disk is required in the final harmonic statement. -/

theorem polarRay_eq_circleMap (θ r : ℝ) : polarRay θ r = circleMap 0 r θ := by
  rw [circleMap_zero, Complex.exp_mul_I]
  simp only [polarRay, Complex.ofReal_cos, Complex.ofReal_sin]

theorem add_polarRay_eq_circleMap (c : ℂ) (θ r : ℝ) :
    c + polarRay θ r = circleMap c r θ := by
  rw [polarRay_eq_circleMap, circleMap_zero]
  rfl

theorem integral_polarRay_eq_circleAverage (H : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, H (c + polarRay θ r)) =
      2 * Real.pi * Real.circleAverage H c r := by
  simp_rw [add_polarRay_eq_circleMap]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  have hp : Function.Periodic (fun θ => H (circleMap c r θ)) (2 * Real.pi) :=
    fun θ => by
      change H (circleMap c r (θ + 2 * Real.pi)) = H (circleMap c r θ)
      rw [periodic_circleMap c r θ]
  have heq := hp.intervalIntegral_add_eq (-Real.pi) 0
  have hends : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simp only [hends, zero_add] at heq
  rw [heq, Real.circleAverage_def, smul_eq_mul]
  field_simp

theorem integral_radial_mul_of_integrable (c : ℂ) {ψ H : ℂ → ℝ}
    (hrad : ∀ z, ψ z = ψ (‖z‖ : ℂ))
    (hm : Measurable (fun z => ψ z * H (c + z)))
    (hint : Integrable (fun z => ψ z * H (c + z))) :
    (∫ z : ℂ, ψ z * H (c + z)) =
      ∫ r : ℝ in Ioi 0, (r * ψ (r : ℂ)) * (2 * Real.pi * Real.circleAverage H c r) := by
  have hi := integrable_polar_weight hm hint
  rw [← Complex.integral_comp_polarCoord_symm (fun z => ψ z * H (c + z))]
  simp only [IntegrableOn, polarCoord_target, Measure.volume_eq_prod,
    ← Measure.prod_restrict, smul_eq_mul] at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hpolar (θ : ℝ) : Complex.polarCoord.symm (r, θ) = polarRay θ r := by
    simp only [Complex.polarCoord_symm_apply, polarRay, Complex.ofReal_cos, Complex.ofReal_sin]
  have hψpolar (θ : ℝ) : ψ (Complex.polarCoord.symm (r, θ)) = ψ (r : ℂ) := by
    rw [hrad, hpolar, polarRay_eq_circleMap, norm_circleMap_zero, abs_of_pos hr]
  simp_rw [hψpolar, hpolar, ← mul_assoc]
  rw [integral_const_mul, integral_polarRay_eq_circleAverage]
  ring

theorem integral_radial_mul (c : ℂ) {ψ H : ℂ → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hrad : ∀ z, ψ z = ψ (‖z‖ : ℂ)) (hH : Continuous H) :
    (∫ z : ℂ, ψ z * H (c + z)) =
      ∫ r : ℝ in Ioi 0, (r * ψ (r : ℂ)) * (2 * Real.pi * Real.circleAverage H c r) := by
  have hcont : Continuous (fun z => ψ z * H (c + z)) :=
    hψ.mul (hH.comp (continuous_const.add continuous_id))
  exact integral_radial_mul_of_integrable c hrad hcont.measurable
    (hcont.integrable_of_hasCompactSupport hψc.mul_right)

theorem integral_radial_eq (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hrad : ∀ z, ψ z = ψ (‖z‖ : ℂ)) :
    (∫ z : ℂ, ψ z) = ∫ r : ℝ in Ioi 0, (r * ψ (r : ℂ)) * (2 * Real.pi) := by
  simpa only [mul_one, Real.circleAverage_const] using
    integral_radial_mul 0 hψ hψc hrad (continuous_const : Continuous (fun _ : ℂ => (1 : ℝ)))

theorem integral_radial_mul_harmonic {ψ H : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hrad : ∀ z, ψ z = ψ (‖z‖ : ℂ)) (hsupp : tsupport ψ ⊆ closedBall 0 R)
    (hHharm : HarmonicOnNhd H (closedBall c R)) :
    (∫ z : ℂ, ψ z * H (c + z)) = (∫ z : ℂ, ψ z) * H c := by
  have hcont : Continuous (fun z => ψ z * H (c + z)) := by
    have hh : Continuous (fun z => H (c + z) * ψ z) :=
      continuous_mul_test_of_continuousAt (fun z hz =>
        ((hHharm (c + z) (by
          simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hsupp hz)).1.continuousAt.comp
            (continuous_const.add continuous_id).continuousAt)) hψ
    simpa only [mul_comm] using hh
  rw [integral_radial_mul_of_integrable c hrad hcont.measurable
    (hcont.integrable_of_hasCompactSupport hψc.mul_right), integral_radial_eq ψ hψ hψc hrad,
    ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := hr
  by_cases hrR : r ≤ R
  · have hhr : HarmonicOnNhd H (closedBall c |r|) := by
      rw [abs_of_pos hr0]
      exact hHharm.mono (closedBall_subset_closedBall hrR)
    have hmean := hhr.circleAverage_eq
    rw [hmean]
    ring
  · have hz : ψ (r : ℂ) = 0 := by
      by_contra hh
      have hhR := hsupp (subset_closure hh)
      have : r ≤ R := by simpa only [mem_closedBall, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr0] using hhR
      exact hrR this
    simp only [hz, mul_zero, zero_mul]


end ModifiedCartan

import ModifiedCartan.HarmonicRadialMean
import ModifiedCartan.LogKernel
import FewInflection.Jensen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem integral_ball_eq_circleAverage {H : ℂ → ℝ} (hm : Measurable H)
    {c : ℂ} {R : ℝ} (hint : IntegrableOn H (ball c R)) :
    (∫ z in ball c R, H z) =
      ∫ r in Ioo 0 R, r * (2 * Real.pi * Real.circleAverage H c r) := by
  have hpre : (fun z : ℂ => c + z) ⁻¹' ball c R = ball 0 R := by
    ext z
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have hcomp : IntegrableOn (fun z => H (c + z)) (ball 0 R) := by
    have h := (measurePreserving_add_left (volume : Measure ℂ) c).integrableOn_comp_preimage
      (measurableEmbedding_addLeft c) |>.mpr hint
    simpa only [hpre, Function.comp_def] using h
  let ψ : ℂ → ℝ := (ball 0 R).indicator (fun _ => 1)
  have he : (fun z => ψ z * H (c + z)) = (ball 0 R).indicator (fun z => H (c + z)) := by
    funext z
    by_cases hz : z ∈ ball (0 : ℂ) R <;> simp [ψ, hz]
  have hψ : Measurable ψ := measurable_const.indicator measurableSet_ball
  have hrad (z : ℂ) : ψ z = ψ (‖z‖ : ℂ) := by
    simp only [ψ, indicator, mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  have hpolar := integral_radial_mul_of_integrable c hrad
    (hψ.mul (hm.comp (measurable_const.add measurable_id))) (by
      rw [he]
      exact hcomp.integrable_indicator measurableSet_ball)
  rw [he, integral_indicator measurableSet_ball] at hpolar
  have htranslate := (measurePreserving_add_left (volume : Measure ℂ) c).setIntegral_preimage_emb
    (measurableEmbedding_addLeft c) H (ball c R)
  rw [hpre] at htranslate
  rw [← htranslate, hpolar]
  have heq : (fun r : ℝ => (r * ψ (r : ℂ)) * (2 * Real.pi * Real.circleAverage H c r)) =ᵐ[
      volume.restrict (Ioi 0)]
      (Iio R).indicator (fun r => r * (2 * Real.pi * Real.circleAverage H c r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change 0 < r at hr
    by_cases hrR : r < R <;>
      simp [ψ, indicator, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, hrR]
  rw [integral_congr_ae heq, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio R ∩ Ioi (0 : ℝ) = Ioo 0 R := by
    ext r
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
  rw [hset]

theorem circleAverage_norm_log_le_of_log_upper {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) {c : ℂ} (hc : h c ≠ 0) {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ z ∈ sphere c r, Real.log ‖h z‖ ≤ M) :
    Real.circleAverage (fun z => ‖Real.log ‖h z‖‖) c r ≤ 2 * M - Real.log ‖h c‖ := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hh
  have hi : CircleIntegrable (fun z => Real.log ‖h z‖) c r :=
    (hA.mono (subset_univ (sphere c |r|))).meromorphicOn.circleIntegrable_log_norm
  have hb' := Real.circleAverage_mono (by simpa only [Real.norm_eq_abs] using hi.abs)
    ((circleIntegrable_const (2 * M) c r).sub hi) (f₂ := fun z => 2 * M - Real.log ‖h z‖) (by
      intro z hz
      have hle := hb z (by simpa only [abs_of_pos hr] using hz)
      change |Real.log ‖h z‖| ≤ 2 * M - Real.log ‖h z‖
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [Real.circleAverage_fun_sub (circleIntegrable_const (2 * M) c r) hi, Real.circleAverage_const] at hb'
  change Real.circleAverage (fun z => |Real.log ‖h z‖|) c r ≤ _ at hb'
  simp only [Real.norm_eq_abs]
  have hj := FewInflection.scalar_circleAverage_log_norm_sub_nonneg_at hh hr hc
  linarith

theorem integral_norm_log_ball_le_of_log_upper {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) {c : ℂ} (hc : h c ≠ 0) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hb : ∀ z ∈ closedBall c R, Real.log ‖h z‖ ≤ M) :
    (∫ z in ball c R, ‖Real.log ‖h z‖‖) ≤
      Real.pi * R ^ 2 * (2 * M - Real.log ‖h c‖) := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hh
  have hiC : IntegrableOn (fun z => ‖Real.log ‖h z‖‖) (closedBall c R) :=
    (integrableOn_log_norm_on_compact hA (subset_univ (closedBall c R))
      (isCompact_closedBall c R)).norm
  have hi := hiC.mono_set ball_subset_closedBall
  have hm : Measurable (fun z => ‖Real.log ‖h z‖‖) :=
    Real.measurable_log.comp hh.continuous.measurable.norm |>.norm
  rw [integral_ball_eq_circleAverage hm hi]
  have hbound : (∫ r in Ioo 0 R, r * (2 * Real.pi *
      Real.circleAverage (fun z => ‖Real.log ‖h z‖‖) c r)) ≤
      ∫ r in Ioo 0 R, r * (2 * Real.pi * (2 * M - Real.log ‖h c‖)) := by
    apply integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact mul_nonneg hr.1.le (mul_nonneg (by positivity)
        (Real.circleAverage_nonneg_of_nonneg (fun z _ => norm_nonneg _)))
    · exact ((continuous_id.mul continuous_const).continuousOn.integrableOn_compact
        (isCompact_Icc : IsCompact (Icc 0 R))).mono_set Ioo_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      apply mul_le_mul_of_nonneg_left _ hr.1.le
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * Real.pi)
      exact circleAverage_norm_log_le_of_log_upper hh hc hr.1 hM
        (fun z hz => hb z (closedBall_subset_closedBall hr.2.le (sphere_subset_closedBall hz)))
  apply hbound.trans_eq
  rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR.le, integral_id]
  ring

end
end ModifiedCartan
#print axioms ModifiedCartan.integral_norm_log_ball_le_of_log_upper

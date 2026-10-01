import ModifiedCartan.LogAreaJensen
import ModifiedCartan.SubharmonicMean

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem analytic_log_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ Real.circleAverage (fun z => Real.log ‖f z‖) c r := by
  have hA : AnalyticOnNhd ℂ f (closedBall c |r|) := by simpa only [abs_of_pos hr] using hf
  rw [hA.circleAverage_log_norm hr.ne' hc]
  suffices 0 ≤ ∑ᶠ u : ℂ, (MeromorphicOn.divisor f (closedBall c |r|) u : ℝ) *
      Real.log (r * ‖c - u‖⁻¹) by linarith
  apply finsum_nonneg
  intro u
  by_cases hu : u ∈ closedBall c |r|
  · by_cases huc : u = c
    · subst u
      rw [hA.divisor_apply (by simp), (hf c (mem_closedBall_self hr.le)).analyticOrderAt_eq_zero.mpr hc]
      simp
    · have hd : 0 ≤ (MeromorphicOn.divisor f (closedBall c |r|) u : ℝ) := by
        exact_mod_cast hA.divisor_nonneg u
      have hnorm : ‖c - u‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm', abs_of_pos hr] using hu
      have hpos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun hcu => huc hcu.symm))
      have harg : 1 ≤ r * ‖c - u‖⁻¹ := by
        simpa only [div_eq_mul_inv] using
          (le_div_iff₀ hpos).mpr (by simpa only [one_mul] using hnorm)
      exact mul_nonneg hd (Real.log_nonneg harg)
  · simp [hu]

/-- Local area Jensen inequality with the actual total real logarithm.
The nonzero center is the only place where a finite center value is used. -/
theorem analytic_log_le_disk_mean {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ (Real.pi * R ^ 2)⁻¹ * ∫ z in ball c R, Real.log ‖f z‖ := by
  classical
  let F : ℂ → ℂ := (closedBall c R).piecewise f (fun _ => 0)
  have hF : Measurable F := hf.continuousOn.measurable_piecewise continuousOn_const measurableSet_closedBall
  have hFeq : EqOn F f (closedBall c R) := by
    intro z hz
    exact piecewise_eq_of_mem _ _ _ hz
  have hlogf : IntegrableOn (fun z => Real.log ‖f z‖) (ball c R) :=
    (integrableOn_log_norm_on_compact hf (Subset.refl _) (isCompact_closedBall c R)).mono_set ball_subset_closedBall
  have hlogF : IntegrableOn (fun z => Real.log ‖F z‖) (ball c R) :=
    hlogf.congr_fun (fun z hz => by rw [hFeq (ball_subset_closedBall hz)]) measurableSet_ball
  have : IsFiniteMeasure (volume.restrict (ball c R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c R).measure_lt_top⟩
  have hpolar := integral_ball_eq_circleAverage (H := fun z => Real.log ‖F z‖ - Real.log ‖f c‖)
    ((Real.measurable_log.comp hF.norm).sub measurable_const)
    (hlogF.sub (integrable_const (Real.log ‖f c‖)))
  have hnonneg : 0 ≤ ∫ z in ball c R, Real.log ‖F z‖ - Real.log ‖f c‖ := by
    rw [hpolar]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hsub : closedBall c |r| ⊆ closedBall c R := by
      rw [abs_of_pos hr.1]
      exact closedBall_subset_closedBall hr.2.le
    have hci : CircleIntegrable (fun z => Real.log ‖f z‖) c r :=
      ((hf.mono hsub).mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    have he : Real.circleAverage (fun z => Real.log ‖F z‖ - Real.log ‖f c‖) c r =
        Real.circleAverage (fun z => Real.log ‖f z‖) c r - Real.log ‖f c‖ := by
      calc
        _ = Real.circleAverage (fun z => Real.log ‖f z‖ - Real.log ‖f c‖) c r := by
          apply Real.circleAverage_congr_sphere
          intro z hz
          dsimp only
          rw [hFeq (hsub (sphere_subset_closedBall hz))]
        _ = _ := by rw [Real.circleAverage_fun_sub hci (circleIntegrable_const _ _ _), Real.circleAverage_const]
    rw [he]
    exact mul_nonneg hr.1.le (mul_nonneg (by positivity)
      (sub_nonneg.mpr (analytic_log_le_circleAverage hr.1
        (hf.mono (closedBall_subset_closedBall hr.2.le)) hc)))
  rw [integral_sub hlogF (integrable_const _), setIntegral_const, smul_eq_mul] at hnonneg
  have he : (∫ z in ball c R, Real.log ‖F z‖) = ∫ z in ball c R, Real.log ‖f z‖ := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [hFeq (ball_subset_closedBall hz)]
  rw [he] at hnonneg
  change 0 ≤ (∫ z in ball c R, Real.log ‖f z‖) - (volume (ball c R)).toReal * Real.log ‖f c‖ at hnonneg
  rw [complex_ball_real_volume c hR.le] at hnonneg
  have harea : 0 < Real.pi * R ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hR)
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ harea).mpr (by nlinarith)

end
end ModifiedCartan
#print axioms ModifiedCartan.analytic_log_le_disk_mean

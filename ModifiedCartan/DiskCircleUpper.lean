import ModifiedCartan.LogAreaJensen
import ModifiedCartan.DiskAverageApproximation

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A local upper bound for all concentric circle means bounds the disk
mean. This is the area comparison needed in Step 2 of `prop:indices`. -/
theorem diskAverage_le_of_circleAverage_le {H : ℂ → ℝ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hH : ContinuousOn H (closedBall c R))
    (hmean : ∀ r, 0 < r → r < R → Real.circleAverage H c r ≤ M) :
    diskAverage R H c ≤ M := by
  classical
  let F : ℂ → ℝ := (closedBall c R).piecewise H (fun _ => 0)
  have hm : Measurable F := hH.measurable_piecewise continuousOn_const measurableSet_closedBall
  have heq : EqOn F H (closedBall c R) := fun _ hz => piecewise_eq_of_mem _ _ _ hz
  have hiH : IntegrableOn H (ball c R) :=
    (hH.integrableOn_compact (isCompact_closedBall c R)).mono_set ball_subset_closedBall
  have hiF : IntegrableOn F (ball c R) :=
    hiH.congr_fun (fun z hz => (heq (ball_subset_closedBall hz)).symm) measurableSet_ball
  have : IsFiniteMeasure (volume.restrict (ball c R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c R).measure_lt_top⟩
  have hnonneg : 0 ≤ ∫ z in ball c R, M - F z := by
    rw [integral_ball_eq_circleAverage (H := fun z => M - F z)
      (measurable_const.sub hm) ((integrable_const M).sub hiF)]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hsub : sphere c |r| ⊆ closedBall c R := by
      rw [abs_of_pos hr.1]
      exact sphere_subset_closedBall.trans (closedBall_subset_closedBall hr.2.le)
    have he : Real.circleAverage (fun z => M - F z) c r = M - Real.circleAverage H c r := by
      calc
        _ = Real.circleAverage (fun z => M - H z) c r := by
          apply Real.circleAverage_congr_sphere
          intro z hz
          dsimp only
          rw [heq (hsub hz)]
        _ = _ := by rw [Real.circleAverage_fun_sub (circleIntegrable_const _ _ _)
          (hH.mono hsub).circleIntegrable', Real.circleAverage_const]
    rw [he]
    exact mul_nonneg hr.1.le (mul_nonneg (by positivity) (sub_nonneg.mpr (hmean r hr.1 hr.2)))
  rw [integral_sub (integrable_const _) hiF, setIntegral_const, smul_eq_mul] at hnonneg
  have hint : (∫ z in ball c R, F z) = ∫ z in ball c R, H z :=
    setIntegral_congr_fun measurableSet_ball (fun z hz => heq (ball_subset_closedBall hz))
  rw [hint] at hnonneg
  change 0 ≤ (volume (ball c R)).toReal * M - (∫ z in ball c R, H z) at hnonneg
  rw [complex_ball_real_volume c hR.le] at hnonneg
  rw [diskAverage_eq hR.le, ← div_eq_inv_mul]
  apply (div_le_iff₀ (mul_pos Real.pi_pos (sq_pos_of_pos hR))).mpr
  nlinarith

theorem diskAverage_const_mul {r : ℝ} (hr : 0 ≤ r) (a : ℝ) (f : ℂ → ℝ) (c : ℂ) :
    diskAverage r (fun z => a * f z) c = a * diskAverage r f c := by
  rw [diskAverage_eq hr, diskAverage_eq hr, integral_const_mul]
  ring

theorem LocalLpConvergence.diskAverage_tendsto_const {U : Set ℂ}
    {f : ℕ → ℂ → ℝ} {a : ℝ} (h : LocalLpConvergence 1 U f (fun _ => a))
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall c r ⊆ U) :
    Tendsto (fun ν => diskAverage r (f ν) c) atTop (𝓝 a) := by
  have ht := h.diskAverage_tendstoUniformlyOn (isCompact_closedBall c r) hball hr
    (K := {c}) (by intro z hz; rcases mem_singleton_iff.mp hz with rfl; exact ball_subset_closedBall)
  simpa only [diskAverage_const hr] using ht.tendsto_at (mem_singleton c)

end ModifiedCartan
#print axioms ModifiedCartan.diskAverage_le_of_circleAverage_le

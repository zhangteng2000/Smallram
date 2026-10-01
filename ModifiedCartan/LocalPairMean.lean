import ModifiedCartan.LocalPoissonMajorant
import Mathlib.Analysis.Complex.Harmonic.MeanValue

open scoped Topology
open Filter Set Metric Complex InnerProductSpace
set_option autoImplicit false
namespace ModifiedCartan

theorem local_pair_norm_pos {p q : ℂ → ℂ} {U : Set ℂ}
    (hred : ∀ z ∈ U, p z ≠ 0 ∨ q z ≠ 0) {z : ℂ} (hz : z ∈ U) :
    0 < max ‖p z‖ ‖q z‖ := by
  rcases hred z hz with hp | hq
  · exact (norm_pos_iff.mpr hp).trans_le (le_max_left _ _)
  · exact (norm_pos_iff.mpr hq).trans_le (le_max_right _ _)

theorem local_pair_log_norm_continuous {p q : ℂ → ℂ} {U : Set ℂ}
    (hp : ContinuousOn p U) (hq : ContinuousOn q U)
    (hred : ∀ z ∈ U, p z ≠ 0 ∨ q z ≠ 0) :
    ContinuousOn (fun z => Real.log (max ‖p z‖ ‖q z‖)) U :=
  (hp.norm.sup hq.norm).log (fun _ hz => (local_pair_norm_pos hred hz).ne')

/-- Exact monotonicity of the logarithmic maximum mean for a local reduced
analytic pair. This supplies the local characteristic comparison for `lem:NH`. -/
theorem local_pair_log_mean_mono {p q : ℂ → ℂ} {r R : ℝ}
    (hp : AnalyticOnNhd ℂ p (closedBall 0 R)) (hq : AnalyticOnNhd ℂ q (closedBall 0 R))
    (hred : ∀ z ∈ closedBall (0 : ℂ) R, p z ≠ 0 ∨ q z ≠ 0)
    (hr : 0 < r) (hrR : r ≤ R) :
    Real.circleAverage (fun z => Real.log (max ‖p z‖ ‖q z‖)) 0 r ≤
      Real.circleAverage (fun z => Real.log (max ‖p z‖ ‖q z‖)) 0 R := by
  rcases eq_or_lt_of_le hrR with rfl | hrR
  · exact le_rfl
  have hR := hr.trans hrR
  let U : ℂ → ℝ := fun z => max ‖p z‖ ‖q z‖
  have hUc : ContinuousOn U (closedBall 0 R) := hp.continuousOn.norm.sup hq.continuousOn.norm
  have hUp : ∀ z ∈ closedBall (0 : ℂ) R, 0 < U z := fun _ hz => local_pair_norm_pos hred hz
  have hlog := local_pair_log_norm_continuous hp.continuousOn hq.continuousOn hred
  have hsp : sphere (0 : ℂ) |R| ⊆ closedBall 0 R := by
    rw [abs_of_pos hR]
    exact sphere_subset_closedBall
  have hci : CircleIntegrable (fun z => Real.log (U z)) 0 R :=
    (hlog.mono hsp).circleIntegrable'
  let H : ℂ → ℂ := fun z => Real.circleAverage
    (fun w => herglotzRieszKernel 0 z w • (Real.log (U w) : ℂ)) 0 R
  have hHA : AnalyticOnNhd ℂ H (ball 0 R) := by
    apply analyticOnNhd_circleAverage_herglotzRieszKernel_smul
    exact (Complex.ofRealCLM.continuous.comp_continuousOn (hlog.mono hsp)).circleIntegrable'
  have hHr (z : ℂ) (hz : z ∈ ball 0 R) :
      (H z).re = Real.circleAverage (fun w => poissonKernel 0 z w * Real.log (U w)) 0 R := by
    have he := re_circleAverage_herglotzRieszKernel_smul hci hz
    simpa only [H, ← poissonKernel_eq_re_herglotzRieszKernel, Pi.smul_apply,
      smul_eq_mul, Pi.mul_def] using! he
  have hbound (z : ℂ) (hz : z ∈ ball 0 R) : Real.log (U z) ≤ (H z).re := by
    rw [hHr z hz]
    rcases le_total ‖p z‖ ‖q z‖ with hpq | hqp
    · have hq0 : q z ≠ 0 := by
        apply norm_pos_iff.mp
        simpa only [U, max_eq_right hpq] using hUp z (ball_subset_closedBall hz)
      simpa only [U, max_eq_right hpq] using log_norm_le_local_poisson_majorant hq hq0 hUc hUp
        (fun w _ => le_max_right ‖p w‖ ‖q w‖) hz
    · have hp0 : p z ≠ 0 := by
        apply norm_pos_iff.mp
        simpa only [U, max_eq_left hqp] using hUp z (ball_subset_closedBall hz)
      simpa only [U, max_eq_left hqp] using log_norm_le_local_poisson_majorant hp hp0 hUc hUp
        (fun w _ => le_max_left ‖p w‖ ‖q w‖) hz
  have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 R := by
    rw [abs_of_pos hr]
    exact closedBall_subset_ball hrR
  have hL : HarmonicOnNhd (fun z => (H z).re) (closedBall 0 |r|) :=
    fun z hz => (hHA z (hsub hz)).harmonicAt_re
  have hmean := Real.circleAverage_mono
    (hlog.mono (fun _ hz => ball_subset_closedBall (hsub (sphere_subset_closedBall hz)))).circleIntegrable'
    (hL.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
    (fun z hz => hbound z (hsub (sphere_subset_closedBall hz)))
  rw [hL.circleAverage_eq, hHr 0 (mem_ball_self hR)] at hmean
  have hzmean : Real.circleAverage (fun w => poissonKernel 0 0 w * Real.log (U w)) 0 R =
      Real.circleAverage (fun w => Real.log (U w)) 0 R := by
    apply Real.circleAverage_congr_sphere
    intro w hw
    have hwn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right, abs_of_pos hR] using hw
    simp only [poissonKernel_def, sub_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      hwn, sub_zero, div_self (pow_ne_zero 2 hR.ne'), one_mul]
  rw [hzmean] at hmean
  exact hmean

end ModifiedCartan
#print axioms ModifiedCartan.local_pair_log_mean_mono


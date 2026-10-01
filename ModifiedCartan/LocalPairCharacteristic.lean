import ModifiedCartan.LocalPairMean
import ModifiedCartan.LocalReducedPair
import ModifiedCartan.DiskRegularRadius

open scoped Topology
open Filter Set Metric MeromorphicOn Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan

theorem log_max_eq_posLog_div_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.log (max x y) = Real.posLog (x / y) + Real.log y := by
  rw [Real.posLog_eq_log_max_one (div_nonneg hx hy.le)]
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy, max_eq_left ((div_le_one hy).mpr hxy), Real.log_one, zero_add]
  · rw [max_eq_left hyx, max_eq_right ((one_le_div hy).mpr hyx),
      Real.log_div (hy.trans_le hyx).ne' hy.ne']
    ring

theorem log_max_norm_eq_posLog_div_add (p q : ℂ) (hq : q ≠ 0) :
    Real.log (max ‖p‖ ‖q‖) = Real.posLog ‖p / q‖ + Real.log ‖q‖ := by
  rw [norm_div]
  exact log_max_eq_posLog_div_add (norm_nonneg p) (norm_pos_iff.mpr hq)

/-- The local scalar characteristic is exactly the maximum-norm mean of an
actual reduced analytic numerator/denominator, with the denominator's center term. -/
theorem diskCharacteristic_eq_local_pair_mean {f p q : ℂ → ℂ} {r R : ℝ}
    (hf : MeromorphicOn f (closedBall 0 R))
    (hp : AnalyticOnNhd ℂ p (closedBall 0 R)) (hq : AnalyticOnNhd ℂ q (closedBall 0 R))
    (hred : ∀ z ∈ closedBall (0 : ℂ) R, p z ≠ 0 ∨ q z ≠ 0) (hq0 : q 0 ≠ 0)
    (hfg : f =ᶠ[codiscreteWithin (closedBall 0 R)] (fun z => p z / q z))
    (hdiv : divisor q (closedBall 0 R) = (divisor f (closedBall 0 R))⁻)
    (hr : 0 < r) (hrR : r ≤ R) :
    diskCharacteristic f r =
      Real.circleAverage (fun z => Real.log (max ‖p z‖ ‖q z‖)) 0 r - Real.log ‖q 0‖ := by
  have hR := hr.trans_le hrR
  have hsub : closedBall (0 : ℂ) |r| ⊆ closedBall 0 R := by
    rw [abs_of_pos hr]
    exact closedBall_subset_closedBall hrR
  have hsp : sphere (0 : ℂ) |r| ⊆ closedBall 0 R := fun _ hz => hsub (sphere_subset_closedBall hz)
  have hqa0 := hq 0 (mem_closedBall_self hR.le)
  have hqn := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hq.meromorphicOn
    (disk_meromorphic_order_ne_top hR hq.meromorphicOn hqa0 hq0)
  have heq : (fun z => Real.posLog ‖f z‖) =ᶠ[codiscreteWithin (closedBall 0 R)]
      (fun z => Real.log (max ‖p z‖ ‖q z‖) - Real.log ‖q z‖) := by
    filter_upwards [hfg, hqn] with z hz hzq
    rw [hz]
    have he := log_max_norm_eq_posLog_div_add (p z) (q z) hzq
    linarith
  have hmax : CircleIntegrable (fun z => Real.log (max ‖p z‖ ‖q z‖)) 0 r :=
    ((local_pair_log_norm_continuous hp.continuousOn hq.continuousOn hred).mono hsp).circleIntegrable'
  have hlogq : CircleIntegrable (fun z => Real.log ‖q z‖) 0 r :=
    (hq.meromorphicOn.mono_set hsp).circleIntegrable_log_norm
  have havg := Real.circleAverage_congr_codiscreteWithin
    (heq.filter_mono (codiscreteWithin_mono hsp)) hr.ne'
  rw [Real.circleAverage_fun_sub hmax hlogq] at havg
  have hd : divisor q (closedBall 0 |r|) = (divisor f (closedBall 0 |r|))⁻ := by
    rw [← hq.meromorphicOn.divisor_restrict hsub, hdiv, restrict_negPart, hf.divisor_restrict hsub]
  have hqp : diskPoleCounting q r = 0 := by
    rw [diskPoleCounting, negPart_eq_zero.mpr (hq.mono hsub).divisor_nonneg]
    simp [closedDiskLogCounting]
  have hqz : diskZeroCounting q r = diskPoleCounting f r := by
    rw [diskZeroCounting, hd, posPart_eq_self.mpr (negPart_nonneg _)]
    rfl
  have hj := diskCounting_jensen hr.ne' (hq.meromorphicOn.mono_set hsub)
  rw [hqp, hqz, hqa0.meromorphicTrailingCoeffAt_of_ne_zero hq0, sub_zero] at hj
  rw [diskCharacteristic, ValueDistribution.proximity_top, havg]
  linarith

/-- Exact radius comparison for the manuscript's local scalar characteristic.
No global meromorphic extension is required. -/
theorem diskCharacteristic_mono {f : ℂ → ℂ} {r R : ℝ}
    (hf : MeromorphicOn f (closedBall 0 R)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hr : 0 < r) (hrR : r ≤ R) : diskCharacteristic f r ≤ diskCharacteristic f R := by
  have hR := hr.trans_le hrR
  have hD0 : divisor f (closedBall 0 R) 0 = 0 := by
    rw [hf.divisor_apply (mem_closedBall_self hR.le), hfa.meromorphicOrderAt_eq,
      hfa.analyticOrderAt_eq_zero.mpr h0]
    rfl
  obtain ⟨p, q, hp, hq, hred, hfg, hdiv, hqne⟩ := local_reduced_pair_of_finite_divisor hf
    (fun w => disk_meromorphic_order_ne_top hR hf hfa h0 w w.property)
    ((divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall ..))
  have hqA := (Complex.analyticOnNhd_univ_iff_differentiable.mpr hq).mono (subset_univ (closedBall 0 R))
  rw [diskCharacteristic_eq_local_pair_mean hf hp hqA hred (hqne 0 hD0) hfg hdiv hr hrR,
    diskCharacteristic_eq_local_pair_mean hf hp hqA hred (hqne 0 hD0) hfg hdiv hR le_rfl]
  exact sub_le_sub_right (local_pair_log_mean_mono hp hqA hred hr hrR) _

end ModifiedCartan
#print axioms ModifiedCartan.diskCharacteristic_eq_local_pair_mean
#print axioms ModifiedCartan.diskCharacteristic_mono

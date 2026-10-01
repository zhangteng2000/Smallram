import ModifiedCartan.DiskCircleUpper
import ModifiedCartan.ArbitraryScaleHypotheses
import ModifiedCartan.RescaledGauge

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem LocalLpConvergence.diskAverage_tendsto {U : Set ℂ}
    {f : ℕ → ℂ → ℝ} {v : ℂ → ℝ} (h : LocalLpConvergence 1 U f v)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hball : closedBall c R ⊆ U) :
    Tendsto (fun ν => diskAverage R (f ν) c) atTop (𝓝 (diskAverage R v c)) := by
  have ht := h.diskAverage_tendstoUniformlyOn (isCompact_closedBall c R) hball hR
    (K := {c}) (by intro z hz; rcases mem_singleton_iff.mp hz with rfl; exact ball_subset_closedBall)
  exact ht.tendsto_at (mem_singleton c)

theorem diskAverage_limit_le_of_circle_means {U : Set ℂ}
    {f : ℕ → ℂ → ℝ} {v : ℂ → ℝ} {M : ℕ → ℝ} {b R : ℝ}
    (hR : 0 < R) (hball : closedBall (0 : ℂ) R ⊆ U)
    (hlim : LocalLpConvergence 1 U f v) (hM : Tendsto M atTop (𝓝 b))
    (hdata : ∀ᶠ ν in atTop, ContinuousOn (f ν) (closedBall 0 R) ∧
      ∀ t : ℝ, 0 < t → t < R → Real.circleAverage (f ν) 0 t ≤ M ν) :
    diskAverage R v 0 ≤ b := by
  apply le_of_tendsto_of_tendsto (hlim.diskAverage_tendsto hR hball) hM
  exact hdata.mono (fun ν hν => diskAverage_le_of_circleAverage_le hR hν.1 hν.2)

/-- The small-radius bound is uniform in the radius after passage to
the limit. Monotonicity controls all inner circle means by the outer one. -/
theorem arbitrary_norm_limit_disk_average_bound {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hερ : ε < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {H : ℕ → ℂ → ℂ} {e : ℕ → ℝ}
    (hH : ∀ᶠ ν in atTop, AnalyticOnNhd ℂ (H ν) (ball 0 64))
    (he : Tendsto e atTop (𝓝 0))
    (hmean : ∀ᶠ ν in atTop, ∀ R : ℝ, 0 < R → R < 64 →
      Real.circleAverage (fun z => (characteristic f (r ν))⁻¹ * Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r ν) (H ν) j z))) 0 R =
          characteristic f (R * r ν) / characteristic f (r ν) + e ν)
    {v : ℂ → ℝ} (hlim : LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (characteristic f (r ν))⁻¹ * Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r ν) (H ν) j z))) v) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → R < 1 →
      diskAverage R v 0 ≤ C * R ^ (ρ - ε) := by
  obtain ⟨C, r0, hC, hr0, hbound⟩ := Paper.lem_power_bounds (characteristic f)
    (fun r hr => characteristic_pos_of_transcendental f htrans hr) (characteristic_monotoneOn f)
    (characteristic_unbounded_of_transcendental f htrans) hρ hl hu hε hερ
  refine ⟨C, zero_lt_one.trans_le hC, ?_⟩
  intro R hR hR1
  have hR4 : R < 4 := hR1.trans (by norm_num)
  have hratio : ∀ᶠ ν in atTop,
      characteristic f (R * r ν) / characteristic f (r ν) ≤ C * R ^ (ρ - ε) := by
    have hRr : Tendsto (fun ν => R * r ν) atTop atTop := Tendsto.const_mul_atTop hR hr
    filter_upwards [hr.eventually_ge_atTop r0, hRr.eventually_ge_atTop r0] with ν hν hRν
    have hh := (hbound R (r ν) hν hRν).2
    rw [max_eq_left (Real.rpow_le_rpow_of_exponent_ge hR hR1.le (by linarith))] at hh
    exact hh
  apply diskAverage_limit_le_of_circle_means hR (closedBall_subset_ball hR4) hlim
    (M := fun ν => C * R ^ (ρ - ε) + e ν)
  · simpa only [add_zero] using tendsto_const_nhds.add he
  · filter_upwards [hH, hmean, hratio, hr.eventually_gt_atTop 0] with ν hHν hmν hbν hrν
    have hc : ContinuousOn
        (fun z => Real.log (euclideanNorm (fun j => rescaledRepresentation f (r ν) (H ν) j z)))
        (ball (0 : ℂ) 64) := by
      simpa only [rescaledRepresentation_log_norm, Function.comp_def, Pi.mul_apply, Pi.sub_apply, id_eq] using!
        ((curve_log_euclideanNorm_continuous f).comp (continuous_const.mul continuous_id)).continuousOn.sub
          (Complex.continuous_re.comp_continuousOn hHν.continuousOn)
    refine ⟨(continuousOn_const.mul hc).mono
      (closedBall_subset_ball (hR1.trans (by norm_num : (1 : ℝ) < 64))), ?_⟩
    intro t ht htR
    rw [hmν t ht (htR.trans (hR1.trans (by norm_num : (1 : ℝ) < 64)))]
    have hmono := characteristic_monotoneOn f (mul_pos ht hrν) (mul_pos hR hrν)
      (mul_le_mul_of_nonneg_right htR.le hrν.le)
    exact add_le_add (le_trans (div_le_div_of_nonneg_right hmono
      (characteristic_pos_of_transcendental f htrans hrν).le) hbν) le_rfl

end ModifiedCartan
#print axioms ModifiedCartan.arbitrary_norm_limit_disk_average_bound

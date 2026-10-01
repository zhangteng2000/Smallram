import ModifiedCartan.AnalyticLogRadialIntegral
import ModifiedCartan.MonotoneWeightedIntegrals

open scoped Topology
open Filter Set Metric MeasureTheory MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

/-- Local L1 convergence of normalized analytic logarithms with a continuous
limit determines their means on every interior circle. Auxiliary to `thm:A` (b). -/
theorem normalized_analytic_log_circleAverage_tendsto
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {B : ℝ}
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) (ball 0 B))
    (hn : ∀ ν, ∃ z ∈ ball (0 : ℂ) B, f ν z ≠ 0)
    (hs : ∀ ν, 0 < s ν)
    (hlim : LocalLpConvergence 1 (ball (0 : ℂ) B)
      (fun ν z => (s ν)⁻¹ * Real.log ‖f ν z‖) u)
    (hu : ContinuousOn u (ball 0 B)) :
    ∀ t : ℝ, 0 < t → t < B →
      Tendsto (fun ν => (s ν)⁻¹ * Real.circleAverage (fun z => Real.log ‖f ν z‖) 0 t)
        atTop (𝓝 (Real.circleAverage u 0 t)) := by
  let F : ℕ → ℝ → ℝ := fun ν t =>
    (s ν)⁻¹ * Real.circleAverage (fun z => Real.log ‖f ν z‖) 0 t
  let g : ℝ → ℝ := Real.circleAverage u 0
  have hmeans (ν : ℕ) := analytic_log_circleAverage_continuous_monotone (hf ν) (hn ν)
  have hcF (ν : ℕ) : ContinuousOn (F ν) (Ioo 0 B) :=
    continuousOn_const.mul (hmeans ν).1
  have hmF (ν : ℕ) : MonotoneOn (F ν) (Ioo 0 B) := by
    intro a ha b hb hab
    exact mul_le_mul_of_nonneg_left ((hmeans ν).2 ha hb hab) (inv_nonneg.mpr (hs ν).le)
  have hcg : ContinuousOn g (Ioo 0 B) := by
    apply Real.ContinuousOn.circleAverage _ (fun t ht => ht.1.le)
    apply hu.mono
    intro z hz
    simpa only [mem_ball, dist_zero_right, sub_zero] using hz.2
  have ho (ν : ℕ) (z : ℂ) (hz : z ∈ ball (0 : ℂ) B) : meromorphicOrderAt (f ν) z ≠ ⊤ := by
    obtain ⟨w, hw, hnw⟩ := hn ν
    have how : meromorphicOrderAt (f ν) w ≠ ⊤ := by
      rw [(hf ν w hw).meromorphicOrderAt_eq, (hf ν w hw).analyticOrderAt_eq_zero.mpr hnw]
      simp
    exact (hf ν).meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_ball (0 : ℂ) B).isPreconnected hw hz how
  have hiF (ν : ℕ) (R : ℝ) (hR : 0 < R) (hRB : R < B) :
      IntervalIntegrable (fun t => t * F ν t) volume 0 R := by
    have hi := (analytic_log_circleAverage_weighted_integrable hR
      ((hf ν).mono (closedBall_subset_ball hRB))
      (fun z => ho ν z (closedBall_subset_ball hRB z.property))).const_mul ((s ν)⁻¹)
    convert hi using 1
    funext t
    dsimp only [F]
    ring
  have hig (R : ℝ) (hR : 0 < R) (hRB : R < B) :
      IntervalIntegrable (fun t => t * g t) volume 0 R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hR.le
    apply continuousOn_id.mul
    apply Real.ContinuousOn.circleAverage _ (fun t ht => ht.1)
    apply hu.mono
    intro z hz
    rw [mem_ball, dist_zero_right]
    have hzR : ‖z‖ ≤ R := by simpa only [sub_zero] using hz.2
    exact hzR.trans_lt hRB
  have hprimitive (R : ℝ) (hR : 0 < R) (hRB : R < B) :
      Tendsto (fun ν => ∫ t in (0 : ℝ)..R, t * F ν t) atTop
        (𝓝 (∫ t in (0 : ℝ)..R, t * g t)) := by
    have he (ν : ℕ) : (∫ t in (0 : ℝ)..R, t * F ν t) =
        (∫ z in ball (0 : ℂ) R, (s ν)⁻¹ * Real.log ‖f ν z‖) / (2 * Real.pi) := by
      have hp := integral_ball_log_norm_eq_radial_mean hR ((hf ν).mono (closedBall_subset_ball hRB))
      rw [integral_const_mul, hp]
      have hmul : (fun t => t * F ν t) = fun t =>
          (s ν)⁻¹ * (t * Real.circleAverage (fun z => Real.log ‖f ν z‖) 0 t) := by
        funext t
        dsimp only [F]
        ring
      rw [hmul, intervalIntegral.integral_const_mul]
      field_simp
    have heu : (∫ z in ball (0 : ℂ) R, u z) / (2 * Real.pi) =
        ∫ t in (0 : ℝ)..R, t * g t := by
      rw [integral_ball_eq_radial_mean_of_continuousOn hR
        (hu.mono (closedBall_subset_ball hRB)) (fun _ _ _ => rfl),
        mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
    have ht := (hlim.integral_ball_tendsto hR (closedBall_subset_ball hRB)).div_const (2 * Real.pi)
    rw [heu] at ht
    exact ht.congr' (Eventually.of_forall (fun ν => (he ν).symm))
  apply tendsto_of_monotone_weighted_integrals (Eventually.of_forall hcF)
    (Eventually.of_forall hmF) hcg
  intro a b ha hab hb
  have he (ν : ℕ) := intervalIntegral.integral_interval_sub_left (μ := volume)
    (hiF ν b (ha.trans hab) hb) (hiF ν a ha (hab.trans hb))
  have heg := intervalIntegral.integral_interval_sub_left (μ := volume)
    (hig b (ha.trans hab) hb) (hig a ha (hab.trans hb))
  simpa only [he, heg] using (hprimitive b (ha.trans hab) hb).sub (hprimitive a ha (hab.trans hb))

end ModifiedCartan
#print axioms ModifiedCartan.normalized_analytic_log_circleAverage_tendsto

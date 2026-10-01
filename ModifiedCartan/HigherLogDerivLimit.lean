import ModifiedCartan.HigherLogDerivSubsequence
import ModifiedCartan.LocalLogHypotheses

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem LocalLpConvergence.higher_logDeriv_localMeasure_on_ball
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {c : ℂ} {r R : ℝ}
    (hu : LocalLpConvergence 1 (ball c R) (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0)
    (hs0 : ∀ n, 0 < s n) (hs : Tendsto s atTop atTop)
    (hr : 0 < r) (hrR : r < R) {j : ℕ} (hj : 0 < j) :
    LocalMeasureConvergence (ball c r)
      (fun n z => iteratedDeriv j (logDeriv (f n)) z / (s n : ℂ) ^ (j + 1)) (fun _ => 0) := by
  apply localMeasureConvergence_of_subseq
  intro ns hns
  obtain ⟨ms, _, hlim⟩ := (hu.comp_tendsto hns).higher_logDeriv_subseq_on_ball
    (fun n => hf (ns n)) (fun n => hnonzero (ns n)) (fun n => hs0 (ns n))
    (hs.comp hns) hr hrR hj
  exact ⟨ms, hlim⟩

theorem exists_positive_tail {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) :
    ∃ N : ℕ, ∀ n : ℕ, 0 < s (n + N) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.eventually (eventually_gt_atTop 0))
  exact ⟨N, fun n => hN (n + N) (Nat.le_add_left _ _)⟩

namespace Paper

/-- LaTeX label `eq:higher-logderiv-measure`, Step 2 of `lem:logderivlimit`.
All higher derivatives of h'/h vanish after the stated normalization. -/
theorem eq_higher_logderiv_measure
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hnonzero : ∀ n, ∃ b ∈ U, f n b ≠ 0)
    (hs : Tendsto s atTop atTop) {j : ℕ} (hj : 0 < j) :
    LocalMeasureConvergence U
      (fun n z => iteratedDeriv j (logDeriv (f n)) z / (s n : ℂ) ^ (j + 1)) (fun _ => 0) := by
  obtain ⟨N, hN⟩ := exists_positive_tail hs
  have htail : LocalMeasureConvergence U
      (fun n z => iteratedDeriv j (logDeriv (f (n + N))) z / (s (n + N) : ℂ) ^ (j + 1)) (fun _ => 0) := by
    apply localMeasureConvergence_of_locally
    intro c hc
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hc
    have hR : closedBall c (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    refine ⟨ball c (ε / 4), isOpen_ball, mem_ball_self (by linarith), ?_⟩
    exact ((hu.comp_tendsto (tendsto_add_atTop_nat N)).restrict
      (ball_subset_closedBall.trans hR)).higher_logDeriv_localMeasure_on_ball
      (fun n => (hf (n + N)).mono hR)
      (fun n => analytic_exists_ne_zero_on_ball hUc (hf (n + N)) (hnonzero (n + N))
        (half_pos hε) (ball_subset_closedBall.trans hR)) hN
      (hs.comp (tendsto_add_atTop_nat N)) (by linarith) (by linarith) hj
  intro K hK hKU ε hε
  exact (tendsto_add_atTop_iff_nat N).mp (htail K hK hKU ε hε)

end Paper


end ModifiedCartan


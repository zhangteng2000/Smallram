import ModifiedCartan.LogLimitSobolev

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Deriving local disk hypotheses for `lem:logderivlimit` from the original
connected-domain nontriviality and normalizer divergence assumptions. The local
Sobolev conclusion here adds no disk nonzero or global sign hypothesis. -/

theorem analytic_exists_ne_zero_on_ball {U : Set ℂ} (hU : IsPreconnected U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hnonzero : ∃ b ∈ U, f b ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hball : ball c R ⊆ U) :
    ∃ b ∈ ball c R, f b ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : f =ᶠ[𝓝 c] 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with z hz
    exact h z hz
  have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU
    (hball (mem_ball_self hR)) hz
  obtain ⟨b, hb, hb0⟩ := hnonzero
  exact hb0 (hall hb)

theorem exists_nonnegative_tail {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) :
    ∃ N : ℕ, ∀ n : ℕ, 0 ≤ s (n + N) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.eventually (eventually_ge_atTop 0))
  exact ⟨N, fun n => hN (n + N) (Nat.le_add_left _ _)⟩

theorem LocalLpConvergence.log_limit_memW1pLoc_on_subdisk
    {U : Set ℂ} (hU : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hnonzero : ∀ n, ∃ b ∈ U, f n b ≠ 0)
    (hs : Tendsto s atTop atTop) {c : ℂ} {r R p : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRU : closedBall c R ⊆ U)
    (hp1 : 1 ≤ p) (hp2 : p < 2) : MemW1pLoc (ENNReal.ofReal p) (ball c r) u := by
  obtain ⟨N, hN⟩ := exists_nonnegative_tail hs
  have hsub : StrictMono (fun n : ℕ => n + N) := fun _ _ h => Nat.add_lt_add_right h N
  have hseq := (hu.comp_strictMono hsub).restrict (ball_subset_closedBall.trans hRU)
  exact hseq.log_limit_memW1pLoc_on_ball (fun n => (hf (n + N)).mono hRU)
    (fun n => analytic_exists_ne_zero_on_ball hU (hf (n + N)) (hnonzero (n + N))
      (by linarith) (ball_subset_closedBall.trans hRU)) hN hr hrR hp1 hp2

theorem LocalLpConvergence.log_limit_locally_memW1pLoc
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hnonzero : ∀ n, ∃ b ∈ U, f n b ≠ 0)
    (hs : Tendsto s atTop atTop) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) :
    ∀ c ∈ U, ∃ r > 0, ball c r ⊆ U ∧ MemW1pLoc (ENNReal.ofReal p) (ball c r) u := by
  intro c hc
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hc
  have hR : closedBall c (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  refine ⟨ε / 4, by linarith, ?_, ?_⟩
  · exact (ball_subset_ball (by linarith)).trans hεU
  · exact hu.log_limit_memW1pLoc_on_subdisk hUc hf hnonzero hs
      (by linarith) (by linarith) hR hp1 hp2



end ModifiedCartan



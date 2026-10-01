import ModifiedCartan.LogDerivSubsequence
import ModifiedCartan.LocalLpGluing
import ModifiedCartan.LogLimitRegularity
import ModifiedCartan.LogDerivativeLp

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem LocalLpConvergence.logDeriv_localLp_on_ball
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {g : ℂ → ℂ} {c : ℂ} {r R p : ℝ}
    (hu : LocalLpConvergence 1 (ball c R) (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0) (hs : ∀ n, 0 ≤ s n)
    (hr : 0 < r) (hrR : r < R) (hg : HasWeakComplexGradient (ball c r) u g)
    (hp1 : 1 ≤ p) (hp2 : p < 2) :
    LocalLpConvergence (ENNReal.ofReal p) (ball c r) (fun n z => (s n)⁻¹ • logDeriv (f n) z) g := by
  apply localLpConvergence_of_subseq
  · intro K hK hKU n
    exact (memLp_logDeriv_on_compact (hf n)
      (hKU.trans ((ball_subset_ball hrR.le).trans ball_subset_closedBall)) hK
      (by linarith) hp2).const_smul ((s n)⁻¹)
  · intro ns hns
    obtain ⟨ms, _, hlim⟩ := (hu.comp_tendsto hns).logDeriv_subseq_on_ball
      (fun n => hf (ns n)) (fun n => hnonzero (ns n)) (fun n => hs (ns n)) hr hrR hg
    exact ⟨ms, hlim p hp1 hp2⟩

theorem LocalLpConvergence.logDeriv_localLpConvergence
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hnonzero : ∀ n, ∃ b ∈ U, f n b ≠ 0)
    (hs : Tendsto s atTop atTop) (hg : HasWeakComplexGradient U u g)
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) :
    LocalLpConvergence (ENNReal.ofReal p) U (fun n z => (s n)⁻¹ • logDeriv (f n) z) g := by
  have hp0 : (ENNReal.ofReal p) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hsource K (hK : IsCompact K) (hKU : K ⊆ U) (n : ℕ) :
      MemLp (fun z => (s n)⁻¹ • logDeriv (f n) z) (ENNReal.ofReal p) (volume.restrict K) :=
    (memLp_logDeriv_on_compact (hf n) hKU hK (by linarith) hp2).const_smul ((s n)⁻¹)
  have hlimit K (hK : IsCompact K) (hKU : K ⊆ U) :
      MemLp g (ENNReal.ofReal p) (volume.restrict K) :=
    (hu.log_limit_memW1pLoc hU hUc hf hnonzero hs hp1 hp2).gradient_memLp hU hg hK hKU
  obtain ⟨N, hN⟩ := exists_nonnegative_tail hs
  have htail : LocalLpConvergence (ENNReal.ofReal p) U
      (fun n z => (s (n + N))⁻¹ • logDeriv (f (n + N)) z) g := by
    apply localLpConvergence_of_locally hp0 ENNReal.ofReal_ne_top
      (fun K hK hKU n => hsource K hK hKU (n + N)) hlimit
    intro c hc
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hc
    have hR : closedBall c (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hrU : ball c (ε / 4) ⊆ U := (ball_subset_ball (by linarith)).trans hεU
    refine ⟨ball c (ε / 4), isOpen_ball, mem_ball_self (by linarith), ?_⟩
    exact ((hu.comp_tendsto (tendsto_add_atTop_nat N)).restrict
      (ball_subset_closedBall.trans hR)).logDeriv_localLp_on_ball
      (fun n => (hf (n + N)).mono hR)
      (fun n => analytic_exists_ne_zero_on_ball hUc (hf (n + N)) (hnonzero (n + N))
        (half_pos hε) (ball_subset_closedBall.trans hR)) hN
      (by linarith) (by linarith) (hg.restrict hrU) hp1 hp2
  refine ⟨hsource, hlimit, ?_⟩
  intro K hK hKU
  exact (tendsto_add_atTop_iff_nat N).mp (htail.tendsto K hK hKU)

namespace Paper

/-- LaTeX label `eq:first-logderiv-limit`, Step 1 of `lem:logderivlimit`.
The real function u is its L1 representative; no extra pointwise regularity is
required. The complex gradient is exactly the encoding of 2∂u. -/
theorem eq_first_logderiv_limit
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hnonzero : ∀ n, ∃ b ∈ U, f n b ≠ 0)
    (hs : Tendsto s atTop atTop) :
    ∃ g : ℂ → ℂ, HasWeakComplexGradient U u g ∧ ∀ p : ℝ, 1 ≤ p → p < 2 →
      LocalLpConvergence (ENNReal.ofReal p) U
        (fun n z => deriv (f n) z / ((s n : ℂ) * f n z)) g := by
  obtain ⟨g, hg, _⟩ := hu.log_limit_weak_gradient hU hUc hf hnonzero hs
  refine ⟨g, hg, ?_⟩
  intro p hp1 hp2
  apply (hu.logDeriv_localLpConvergence hU hUc hf hnonzero hs hg hp1 hp2).congr_ae _ EventuallyEq.rfl
  intro n
  apply Eventually.of_forall
  intro z
  simp [logDeriv_apply, Complex.real_smul, div_eq_mul_inv, mul_comm, mul_assoc]

end Paper


end ModifiedCartan


import ModifiedCartan.LocalLogHypotheses
import ModifiedCartan.SobolevLocality

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Sobolev regularity and a single weak gradient on the manuscript's whole
open connected domain, supporting `lem:logderivlimit`. The proof derives local
nontriviality and tail positivity, then glues the constructed local gradients. -/

theorem LocalLpConvergence.log_limit_memW1pLoc
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hnonzero : ∀ n, ∃ b ∈ U, f n b ≠ 0)
    (hs : Tendsto s atTop atTop) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) :
    MemW1pLoc (ENNReal.ofReal p) U u := by
  apply MemW1pLoc.of_locally (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
    ENNReal.ofReal_ne_top
  intro x hx
  obtain ⟨r, hr, hrU, hSob⟩ := hu.log_limit_locally_memW1pLoc hU hUc hf hnonzero hs hp1 hp2 x hx
  exact ⟨ball x r, isOpen_ball, mem_ball_self hr, hrU, hSob⟩

theorem LocalLpConvergence.log_limit_weak_gradient
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hnonzero : ∀ n, ∃ b ∈ U, f n b ≠ 0)
    (hs : Tendsto s atTop atTop) :
    ∃ g : ℂ → ℂ, HasWeakComplexGradient U u g ∧
      ∀ p : ℝ, 1 ≤ p → p < 2 → ∀ K, IsCompact K → K ⊆ U →
        MemLp u (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp g (ENNReal.ofReal p) (volume.restrict K) := by
  obtain ⟨g, hg, _, _⟩ := hu.log_limit_memW1pLoc hU hUc hf hnonzero hs (p := 1) le_rfl (by norm_num)
  refine ⟨g, hg, ?_⟩
  intro p hp1 hp2 K hK hKU
  have hSob := hu.log_limit_memW1pLoc hU hUc hf hnonzero hs hp1 hp2
  refine ⟨?_, hSob.gradient_memLp hU hg hK hKU⟩
  obtain ⟨_, _, hmem, _⟩ := hSob
  exact hmem K hK hKU




end ModifiedCartan



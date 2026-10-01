import ModifiedCartan.AveragedL1Compactness
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem tendsto_toL1_of_eLpNorm {μ : Measure ℂ} {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (h : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toL1 (f n)) atTop (𝓝 (hg.toL1 g)) := by
  apply EMetric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually_lt_const hε)
  refine ⟨N, fun n hn => ?_⟩
  simp only [Integrable.toL1, Lp.edist_toLp_toLp]
  exact hN n hn

theorem totallyBounded_l1_range_of_subsequences {μ : Measure ℂ} {f : ℕ → ℂ → ℝ}
    (hf : ∀ n, Integrable (f n) μ)
    (h : ∀ k : ℕ → ℕ, ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ g : ℂ → ℝ,
      Integrable g μ ∧ Tendsto (fun n => eLpNorm (f (k (ns n)) - g) 1 μ) atTop (𝓝 0)) :
    TotallyBounded (range (fun n => (hf n).toL1 (f n))) := by
  apply totallyBounded_of_cauchy_subsequences
  intro v hv
  choose k hk using hv
  obtain ⟨ns, hns, g, hg, hconv⟩ := h k
  refine ⟨ns, hns, ?_⟩
  have hc := (tendsto_toL1_of_eLpNorm (fun n => hf (k (ns n))) hg hconv).cauchySeq
  convert! hc using 1
  funext n
  exact (hk (ns n)).symm

/-- One subsequence converges simultaneously in a countable family of L1 spaces. -/
theorem exists_common_l1_subsequence {ι : Type*} [Countable ι]
    (μ : ι → Measure ℂ) {f : ℕ → ℂ → ℝ}
    (hf : ∀ i n, Integrable (f n) (μ i))
    (hcompact : ∀ i, TotallyBounded (range (fun n => (hf i n).toL1 (f n)))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ g : ∀ i, Lp ℝ 1 (μ i),
      ∀ i, Tendsto (fun n => (hf i (ns n)).toL1 (f (ns n))) atTop (𝓝 (g i)) := by
  let F : ℕ → ∀ i, Lp ℝ 1 (μ i) := fun n i => (hf i n).toL1 (f n)
  have hc : IsCompact {v : ∀ i, Lp ℝ 1 (μ i) |
      ∀ i, v i ∈ closure (range (fun n => (hf i n).toL1 (f n)))} :=
    isCompact_pi_infinite (fun i => (hcompact i).closure.isCompact_of_isClosed isClosed_closure)
  obtain ⟨g, _, ns, hns, hlim⟩ := hc.tendsto_subseq (x := F)
    (fun n i => subset_closure (mem_range_self n))
  exact ⟨ns, hns, g, fun i => tendsto_pi_nhds.mp hlim i⟩


end ModifiedCartan

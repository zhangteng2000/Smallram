import ModifiedCartan.LocalizedMeasures
import ModifiedCartan.LogWeak
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric TopologicalSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! Weakly convergent subsequences of the actual localized zero-counting
measures in Step 1 of `lem:logderivlimit`. The proof uses the proved compactness
and metrizability of probability measures, then restores their total masses.
The same subsequence gives convergence of logarithmic potentials and Cauchy
transforms. A whole-sequence conclusion is a separate later step. -/

theorem finiteMeasure_tendsto_subseq_of_compactSpace {E : Type*}
    [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompactSpace E] [Nonempty E]
    (ν : ℕ → FiniteMeasure E) (C : ℝ≥0) (hC : ∀ n, (ν n).mass ≤ C) :
    ∃ (ν₀ : FiniteMeasure E) (ns : ℕ → ℕ), StrictMono ns ∧
      Tendsto (ν ∘ ns) atTop (𝓝 ν₀) := by
  let q (n : ℕ) : ℝ≥0 × ProbabilityMeasure E := ((ν n).mass, (ν n).normalize)
  have hq (n : ℕ) : q n ∈ (Icc 0 C) ×ˢ (univ : Set (ProbabilityMeasure E)) :=
    ⟨⟨zero_le, hC n⟩, mem_univ _⟩
  obtain ⟨p, _, ns, hns, ht⟩ := (isCompact_Icc.prod isCompact_univ).tendsto_subseq hq
  let g : ℝ≥0 × ProbabilityMeasure E → FiniteMeasure E := fun p => p.1 • p.2.toFiniteMeasure
  have hg : Continuous g := continuous_fst.smul
    ((ProbabilityMeasure.toFiniteMeasure_isEmbedding E).continuous.comp continuous_snd)
  refine ⟨g p, ns, hns, ?_⟩
  simpa only [Function.comp_def, g, q, ← FiniteMeasure.self_eq_mass_smul_normalize]
    using (hg.tendsto p).comp ht

theorem map_comap_subtype_finiteMeasure {K : Set ℂ} (hK : IsClosed K)
    (ν : FiniteMeasure ℂ) (hsupp : ∀ᵐ a ∂(ν : Measure ℂ), a ∈ K) :
    (ν.comap (Subtype.val : K → ℂ)).map Subtype.val = ν := by
  apply Subtype.ext
  change ((ν : Measure ℂ).comap Subtype.val).map Subtype.val = (ν : Measure ℂ)
  have hf : Topology.IsClosedEmbedding (Subtype.val : K → ℂ) :=
    Topology.IsClosedEmbedding.subtypeVal hK
  rw [hf.measurableEmbedding.map_comap]
  simpa only [Subtype.range_val] using Measure.restrict_eq_self_of_ae_mem hsupp

theorem finiteMeasure_tendsto_subseq_of_compact_support (ν : ℕ → FiniteMeasure ℂ)
    {K : Set ℂ} (hK : IsCompact K) (hsupp : ∀ n, ∀ᵐ a ∂(ν n : Measure ℂ), a ∈ K)
    (C : ℝ≥0) (hC : ∀ n, (ν n).mass ≤ C) :
    ∃ (ν₀ : FiniteMeasure ℂ) (ns : ℕ → ℕ), StrictMono ns ∧
      Tendsto (ν ∘ ns) atTop (𝓝 ν₀) ∧ ∀ᵐ a ∂(ν₀ : Measure ℂ), a ∈ K := by
  classical
  by_cases hne : K.Nonempty
  · let : Nonempty K := hne.to_subtype
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let μ (n : ℕ) : FiniteMeasure K := (ν n).comap Subtype.val
    have hm (n : ℕ) : (μ n).mass ≤ C :=
      ((ν n).mass_comap_le Subtype.val).trans (hC n)
    obtain ⟨μ₀, ns, hns, ht⟩ := finiteMeasure_tendsto_subseq_of_compactSpace μ C hm
    have hmap : Tendsto (ν ∘ ns) atTop (𝓝 (μ₀.map Subtype.val)) := by
      have hmapeq (n : ℕ) : (μ n).map Subtype.val = ν n :=
        map_comap_subtype_finiteMeasure hK.isClosed (ν n) (hsupp n)
      simpa only [Function.comp_def, hmapeq] using
        ((FiniteMeasure.continuous_map continuous_subtype_val).tendsto μ₀).comp ht
    exact ⟨μ₀.map Subtype.val, ns, hns, hmap,
      ae_mem_closed_of_weak_tendsto hmap hK.isClosed (fun n => hsupp (ns n))⟩
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hν (n : ℕ) : ν n = 0 := by
      apply Subtype.ext
      apply Measure.measure_univ_eq_zero.mp
      change (ν n : Measure ℂ) univ = 0
      simpa only [hKe, ae_iff, mem_empty_iff_false, not_false_eq_true, ofPred_true] using hsupp n
    refine ⟨0, id, strictMono_id, ?_, ?_⟩
    · simpa only [Function.comp_def, hν] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : FiniteMeasure ℂ)) atTop (𝓝 0))
    · simp


theorem LocalLpConvergence.localizedZeroMeasure_tendsto_subseq {U : Set ℂ}
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hball : ball c R ⊆ U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0) (hs : ∀ n, 0 ≤ s n)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ ball c R) (hχ0 : ∀ a, 0 ≤ χ a) :
    ∃ (ν₀ : FiniteMeasure ℂ) (ns : ℕ → ℕ), StrictMono ns ∧
      Tendsto (fun n => localizedZeroMeasure (hf (ns n)) (s (ns n)) χ hχ.continuous hχc)
        atTop (𝓝 ν₀) ∧ ∀ᵐ a ∂(ν₀ : Measure ℂ), a ∈ tsupport χ := by
  obtain ⟨M, hM0, hM⟩ :=
    hu.localizedZeroMeasure_mass_bounded hball hf hnonzero hs hχ hχc hχU hχ0
  have hmass (n : ℕ) : (localizedZeroMeasure (hf n) (s n) χ hχ.continuous hχc).mass ≤
      (⟨M, hM0.le⟩ : ℝ≥0) := by
    have hm : ((localizedZeroMeasure (hf n) (s n) χ hχ.continuous hχc).mass : ℝ) ≤ M := by
      simpa only [Measure.real, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal] using hM n
    exact_mod_cast hm
  exact finiteMeasure_tendsto_subseq_of_compact_support
    (fun n => localizedZeroMeasure (hf n) (s n) χ hχ.continuous hχc) hχc
    (fun n => localizedZeroMeasure_ae_mem (hf n) (s n) hχ.continuous hχc) ⟨M, hM0.le⟩ hmass


theorem LocalLpConvergence.localizedZeroMeasure_potentials_subseq {U : Set ℂ}
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hball : ball c R ⊆ U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0) (hs : ∀ n, 0 ≤ s n)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ ball c R) (hχ0 : ∀ a, 0 ≤ χ a) :
    ∃ (ν₀ : FiniteMeasure ℂ) (ns : ℕ → ℕ), StrictMono ns ∧
      Tendsto (fun n => localizedZeroMeasure (hf (ns n)) (s (ns n)) χ hχ.continuous hχc)
        atTop (𝓝 ν₀) ∧
      (∀ᵐ a ∂(ν₀ : Measure ℂ), a ∈ tsupport χ) ∧
      LocalLpConvergence 1 U
        (fun n => logPotential (localizedZeroMeasure (hf (ns n)) (s (ns n)) χ hχ.continuous hχc))
        (logPotential ν₀) ∧
      ∀ p : ℝ, 1 ≤ p → p < 2 → LocalLpConvergence (ENNReal.ofReal p) U
        (fun n => cauchyTransform
          (localizedZeroMeasure (hf (ns n)) (s (ns n)) χ hχ.continuous hχc))
        (cauchyTransform ν₀) := by
  obtain ⟨ν₀, ns, hns, ht, hsupp⟩ :=
    hu.localizedZeroMeasure_tendsto_subseq hball hf hnonzero hs hχ hχc hχU hχ0
  exact ⟨ν₀, ns, hns, ht, hsupp,
    logPotential_localL1Convergence ht hχc
      (fun n => localizedZeroMeasure_ae_mem (hf (ns n)) (s (ns n)) hχ.continuous hχc) U,
    fun _ hp1 hp2 => cauchyTransform_localLpConvergence ht hp1 hp2 U⟩


end ModifiedCartan

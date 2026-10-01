import ModifiedCartan.LocalConvergence

open scoped Topology ENNReal
open Filter MeasureTheory Set

set_option autoImplicit false

namespace ModifiedCartan

/-! Continuous mapping and products for convergence in measure, used in Step 3
of manuscript lemma `lem:logderivlimit`. Proofs use the proved subsequence
criterion and almost-everywhere convergence. -/

theorem tendstoInMeasure_continuous_map
    {α E F : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (h : TendstoInMeasure μ f atTop u)
    {Φ : E → F} (hΦ : Continuous Φ) :
    TendstoInMeasure μ (fun n x => Φ (f n x)) atTop (fun x => Φ (u x)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => hΦ.comp_aestronglyMeasurable (hf n))).mpr
  intro ns hns
  obtain ⟨ms, hms, hAE⟩ := (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hAE] with x hx
  exact (hΦ.tendsto (u x)).comp hx

theorem tendstoInMeasure_continuous_map₂
    {α E F G : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
    [PseudoEMetricSpace F] [PseudoEMetricSpace G]
    {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℕ → α → E} {u : α → E} {g : ℕ → α → F} {v : α → F}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : ∀ n, AEStronglyMeasurable (g n) μ)
    (h : TendstoInMeasure μ f atTop u) (h' : TendstoInMeasure μ g atTop v)
    {Φ : E × F → G} (hΦ : Continuous Φ) :
    TendstoInMeasure μ (fun n x => Φ (f n x, g n x)) atTop (fun x => Φ (u x, v x)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => hΦ.comp_aestronglyMeasurable ((hf n).prodMk (hg n)))).mpr
  intro ns hns
  obtain ⟨ms, hms, hAE⟩ := (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks, hks, hAE'⟩ := ((h'.comp hns.tendsto_atTop).comp hms.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms ∘ ks, hms.comp hks, ?_⟩
  filter_upwards [hAE, hAE'] with x hx hx'
  exact (hΦ.tendsto (u x, v x)).comp ((hx.comp hks.tendsto_atTop).prodMk_nhds hx')

theorem LocalMeasureConvergence.continuous_map
    {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {U : Set ℂ} {f : ℕ → ℂ → E} {u : ℂ → E}
    (h : LocalMeasureConvergence U f u)
    (hf : ∀ K, IsCompact K → K ⊆ U → ∀ n, AEStronglyMeasurable (f n) (volume.restrict K))
    {Φ : E → F} (hΦ : Continuous Φ) :
    LocalMeasureConvergence U (fun n x => Φ (f n x)) (fun x => Φ (u x)) := by
  intro K hK hKU
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact tendstoInMeasure_continuous_map (hf K hK hKU) (h K hK hKU) hΦ

theorem LocalMeasureConvergence.continuous_map₂
    {E F G : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F] [PseudoEMetricSpace G]
    {U : Set ℂ} {f : ℕ → ℂ → E} {u : ℂ → E} {g : ℕ → ℂ → F} {v : ℂ → F}
    (h : LocalMeasureConvergence U f u) (h' : LocalMeasureConvergence U g v)
    (hf : ∀ K, IsCompact K → K ⊆ U → ∀ n, AEStronglyMeasurable (f n) (volume.restrict K))
    (hg : ∀ K, IsCompact K → K ⊆ U → ∀ n, AEStronglyMeasurable (g n) (volume.restrict K))
    {Φ : E × F → G} (hΦ : Continuous Φ) :
    LocalMeasureConvergence U (fun n x => Φ (f n x, g n x)) (fun x => Φ (u x, v x)) := by
  intro K hK hKU
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact tendstoInMeasure_continuous_map₂ (hf K hK hKU) (hg K hK hKU)
    (h K hK hKU) (h' K hK hKU) hΦ


end ModifiedCartan


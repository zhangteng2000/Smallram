import ModifiedCartan.LocalConvergence
import Mathlib.Topology.Compactness.SigmaCompact

open scoped Topology ENNReal
open Filter MeasureTheory Set

namespace ModifiedCartan

/-! One common almost-everywhere subsequence on a full open domain.
This supplies the measure-theoretic extraction used in `lem:sum` and
`lem:logderivlimit`; neither paper lemma is asserted here. -/

theorem exists_seq_tendsto_ae_on_increasing_cover
    {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
    {μ : Measure α} {f : ℕ → α → E} {u : α → E}
    (K : ℕ → Set α) (hK : ∀ n, MeasurableSet (K n)) (hmono : Monotone K)
    (h : ∀ n, TendstoInMeasure (μ.restrict (K n)) f atTop u) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ.restrict (⋃ n, K n), Tendsto (fun n => f (ns n) x) atTop (𝓝 (u x)) := by
  obtain ⟨ns, hns, hbound⟩ := extraction_forall_of_eventually'
    (fun n => ExistsSeqTendstoAe.exists_nat_measure_lt_two_inv (h n) n)
  let S : ℕ → Set α := fun n =>
    {x | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (f (ns n) x) (u x)} ∩ K n
  have hmass : ∀ n, μ (S n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    simpa only [Measure.restrict_apply' (hK n)] using hbound n
  have hsum : (∑' n, μ (S n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hmass)
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      ENNReal.ofNat_ne_top (n := 2)
  have hgood := ae_eventually_notMem hsum
  refine ⟨ns, hns, ?_⟩
  filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem (MeasurableSet.iUnion hK)]
    with x hx hxK
  obtain ⟨m, hm⟩ := mem_iUnion.mp hxK
  have hdist : ∀ᶠ n in atTop, edist (f (ns n) x) (u x) < (2 : ℝ≥0∞)⁻¹ ^ n := by
    filter_upwards [hx, eventually_ge_atTop m] with n hn hmn
    exact lt_of_not_ge (fun hlarge => hn ⟨hlarge, hmono hmn hm⟩)
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ≥0∞)⁻¹ ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  apply EMetric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdist.and (hpow.eventually_lt_const hε))
  exact ⟨N, fun n hn => (hN n hn).1.trans (hN n hn).2⟩

theorem LocalMeasureConvergence.exists_seq_tendsto_ae
    {E : Type*} [PseudoEMetricSpace E] {U : Set ℂ}
    {f : ℕ → ℂ → E} {u : ℂ → E} (h : LocalMeasureConvergence U f u) (hU : IsOpen U) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂volume.restrict U, Tendsto (fun ν => f (ns ν) z) atTop (𝓝 (u z)) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : ℕ → Set ℂ := fun n => Subtype.val '' compactCovering U n
  have hK : ∀ n, IsCompact (K n) := fun n =>
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hKU : ∀ n, K n ⊆ U := by
    intro n z hz
    obtain ⟨y, _, rfl⟩ := hz
    exact y.property
  have hmono : Monotone K := fun i j hij => image_mono (compactCovering_subset U hij)
  have hcover : (⋃ n, K n) = U := by
    simp only [K, ← image_iUnion, iUnion_compactCovering, image_univ, Subtype.range_coe]
  have hseq := exists_seq_tendsto_ae_on_increasing_cover K (fun n => (hK n).measurableSet)
    hmono (fun n => h (K n) (hK n) (hKU n))
  simpa only [hcover] using hseq

theorem LocalLpConvergence.exists_seq_tendsto_ae
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {U : Set ℂ}
    {f : ℕ → ℂ → E} {u : ℂ → E} (h : LocalLpConvergence p U f u)
    (hp : p ≠ 0) (hU : IsOpen U) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂volume.restrict U, Tendsto (fun ν => f (ns ν) z) atTop (𝓝 (u z)) :=
  (h.inMeasure hp).exists_seq_tendsto_ae hU

end ModifiedCartan



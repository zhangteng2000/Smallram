import ModifiedCartan.LocalLpGluing
import ModifiedCartan.LocalSubsequence

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem localL1Convergence_of_eLpNorm_on_set {K V : Set ℂ} (hVK : V ⊆ K)
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    (hf : ∀ n, IntegrableOn (f n) K) (hg : IntegrableOn g K)
    (h : Tendsto (fun n => eLpNorm (f n - g) 1 (volume.restrict K)) atTop (𝓝 0)) :
    LocalLpConvergence 1 V f g where
  source_mem S _ hSV n := memLp_one_iff_integrable.mpr ((hf n).mono_set (hSV.trans hVK))
  limit_mem S _ hSV := memLp_one_iff_integrable.mpr (hg.mono_set (hSV.trans hVK))
  tendsto S _ hSV := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    intro n
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ (hSV.trans hVK))

theorem LocalLpConvergence.ae_unique {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℝ} {g h : ℂ → ℝ} {p : ℝ≥0∞} (hp : p ≠ 0)
    (hg : LocalLpConvergence p U f g) (hh : LocalLpConvergence p U f h) :
    g =ᵐ[volume.restrict U] h := by
  obtain ⟨ns, hns, hgns⟩ := hg.exists_seq_tendsto_ae hp hU
  obtain ⟨ms, hms, hhms⟩ := (hh.comp_strictMono hns).exists_seq_tendsto_ae hp hU
  filter_upwards [hgns, hhms] with z hgz hhz
  exact tendsto_nhds_unique (hgz.comp hms.tendsto_atTop) hhz

theorem exists_localL1_limit_of_countable_cover {ι : Type*} [Countable ι]
    {U : Set ℂ} {V : ι → Set ℂ} (hV : ∀ i, IsOpen (V i))
    (hcover : U ⊆ ⋃ i, V i) {f : ℕ → ℂ → ℝ}
    (hf : ∀ K, IsCompact K → K ⊆ U → ∀ n, IntegrableOn (f n) K)
    (hlocal : ∀ i, ∃ g : ℂ → ℝ, LocalLpConvergence 1 (V i) f g) :
    ∃ g : ℂ → ℝ, LocalLpConvergence 1 U f g := by
  classical
  choose g hg using hlocal
  have hcompat (i j : ι) : g i =ᵐ[volume.restrict (V i ∩ V j)] g j :=
    LocalLpConvergence.ae_unique ((hV i).inter (hV j)) (by norm_num)
      ((hg i).restrict inter_subset_left) ((hg j).restrict inter_subset_right)
  obtain ⟨G, hG⟩ := exists_ae_gluing_countable (fun i => (hV i).measurableSet) g hcompat
  have hloc (i : ι) : LocalLpConvergence 1 (V i) f G :=
    (hg i).congr_ae (fun _ => ae_eq_refl _) (hG i).symm
  have hGint : LocallyIntegrableOn G U := by
    apply locallyIntegrableOn_of_locally
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
    refine ⟨V i, hV i, hxi, (locallyIntegrableOn_iff (hV i).isLocallyClosed).mpr ?_⟩
    intro K hKV hK
    exact memLp_one_iff_integrable.mp ((hloc i).limit_mem K hK hKV)
  refine ⟨G, localLpConvergence_of_locally (by norm_num) (by norm_num) ?_ ?_ ?_⟩
  · intro K hK hKU n
    exact memLp_one_iff_integrable.mpr (hf K hK hKU n)
  · intro K hK hKU
    exact memLp_one_iff_integrable.mpr (hGint.integrableOn_compact_subset hKU hK)
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
    exact ⟨V i, hV i, hxi, hloc i⟩


end ModifiedCartan

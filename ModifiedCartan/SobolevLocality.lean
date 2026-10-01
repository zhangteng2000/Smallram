import ModifiedCartan.WeakGradientLocality

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric TopologicalSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! Local-to-global Sobolev membership for `lem:logderivlimit`. A countable
open subcover and proved AE uniqueness glue the local weak gradients; finite
test partitions and local-to-compact integrability prove the global statement. -/

theorem HasWeakComplexGradient.congr_gradient_ae {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℝ} {g h : ℂ → ℂ} (hg : HasWeakComplexGradient U u g)
    (hgh : g =ᵐ[volume.restrict U] h) : HasWeakComplexGradient U u h where
  function_integrable := hg.function_integrable
  gradient_integrable K hK hKU := (hg.gradient_integrable K hK hKU).congr
    (hgh.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)))
  test_one φ hφ hφc hφU := by
    have heq := integral_mul_test_congr_ae hU.measurableSet (hgh.symm.fun_comp Complex.re) hφU
    simp only [Function.comp_def] at heq
    rw [heq]
    exact hg.test_one φ hφ hφc hφU
  test_I φ hφ hφc hφU := by
    have heq := integral_mul_test_congr_ae hU.measurableSet
      (hgh.symm.fun_comp (fun z : ℂ => -z.im)) hφU
    simp only [Function.comp_def] at heq
    rw [heq]
    exact hg.test_I φ hφ hφc hφU

theorem exists_ae_gluing_countable {ι : Type*} [Countable ι] {E : Type*} [Zero E]
    {V : ι → Set ℂ} (hV : ∀ i, MeasurableSet (V i)) (g : ι → ℂ → E)
    (hcompat : ∀ i j, g i =ᵐ[volume.restrict (V i ∩ V j)] g j) :
    ∃ G : ℂ → E, ∀ i, G =ᵐ[volume.restrict (V i)] g i := by
  classical
  let G (z : ℂ) : E := if hz : ∃ i, z ∈ V i then g (Classical.choose hz) z else 0
  refine ⟨G, ?_⟩
  intro i
  have hall : ∀ᵐ z ∂volume, ∀ j, z ∈ V i ∩ V j → g i z = g j z :=
    ae_all_iff.mpr (fun j => (ae_restrict_iff' ((hV i).inter (hV j))).mp (hcompat i j))
  apply (ae_restrict_iff' (hV i)).mpr
  filter_upwards [hall] with z hz hzV
  have hex : ∃ j, z ∈ V j := ⟨i, hzV⟩
  dsimp only [G]
  rw [dif_pos hex]
  exact (hz _ ⟨hzV, Classical.choose_spec hex⟩).symm

theorem memLp_on_compact_of_locally {E : Type*} [NormedAddCommGroup E]
    {U : Set ℂ} {f : ℂ → E} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hint : ∀ K, IsCompact K → K ⊆ U → IntegrableOn f K)
    (hlocal : ∀ x ∈ U, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧
      ∀ K, IsCompact K → K ⊆ V → MemLp f p (volume.restrict K))
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) : MemLp f p (volume.restrict K) := by
  apply (integrable_norm_rpow_iff (hint K hK hKU).aestronglyMeasurable hp0 hpt).mp
  have hrpow : LocallyIntegrableOn (fun z => ‖f z‖ ^ p.toReal) U := by
    apply locallyIntegrableOn_of_locally
    intro x hx
    obtain ⟨V, hV, hxV, hVmem⟩ := hlocal x hx
    refine ⟨V, hV, hxV, (locallyIntegrableOn_iff hV.isLocallyClosed).mpr ?_⟩
    intro T hTV hT
    exact (hVmem T hT hTV).integrable_norm_rpow hp0 hpt
  exact hrpow.integrableOn_compact_subset hKU hK

theorem MemW1pLoc.of_countable_cover {ι : Type*} [Countable ι]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {U : Set ℂ} {V : ι → Set ℂ}
    (hV : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U) (hcover : U ⊆ ⋃ i, V i)
    {u : ℂ → ℝ} (hlocal : ∀ i, MemW1pLoc p (V i) u) : MemW1pLoc p U u := by
  classical
  choose g hg humem hgmem using hlocal
  have hcompat (i j : ι) : g i =ᵐ[volume.restrict (V i ∩ V j)] g j :=
    ((hg i).restrict inter_subset_left).unique ((hV i).inter (hV j))
      ((hg j).restrict inter_subset_right)
  obtain ⟨G, hG⟩ := exists_ae_gluing_countable (fun i => (hV i).measurableSet) g hcompat
  have hgrad (i : ι) : HasWeakComplexGradient (V i) u G :=
    (hg i).congr_gradient_ae (hV i) (hG i).symm
  have hglobal : HasWeakComplexGradient U u G := by
    apply HasWeakComplexGradient.of_locally
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
    exact ⟨V i, hV i, hxi, hVU i, hgrad i⟩
  refine ⟨G, hglobal, ?_, ?_⟩
  · intro K hK hKU
    apply memLp_on_compact_of_locally hp0 hpt hglobal.function_integrable _ hK hKU
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
    exact ⟨V i, hV i, hxi, humem i⟩
  · intro K hK hKU
    apply memLp_on_compact_of_locally hp0 hpt hglobal.gradient_integrable _ hK hKU
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
    refine ⟨V i, hV i, hxi, ?_⟩
    intro T hT hTV
    exact (memLp_congr_ae ((hG i).symm.filter_mono
      (ae_mono (Measure.restrict_mono_set _ hTV)))).mp (hgmem i T hT hTV)

theorem MemW1pLoc.of_locally {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    {U : Set ℂ} {u : ℂ → ℝ}
    (hlocal : ∀ x ∈ U, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ MemW1pLoc p V u) :
    MemW1pLoc p U u := by
  classical
  choose V hV hxV hVU hSob using (fun x : U => hlocal x x.2)
  have hcover : U ⊆ ⋃ x : U, V x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV _⟩
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable V hV
  letI : Countable T := hT.to_subtype
  have hcover' : U ⊆ ⋃ i : T, V i := by
    intro z hz
    have hz' : z ∈ ⋃ i ∈ T, V i := by rw [hTU]; exact hcover hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz'
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  exact MemW1pLoc.of_countable_cover hp0 hpt (fun i : T => hV i)
    (fun i : T => hVU i) hcover' (fun i : T => hSob i)



theorem MemW1pLoc.gradient_memLp {p : ℝ≥0∞} {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℝ} {g : ℂ → ℂ} (hu : MemW1pLoc p U u)
    (hg : HasWeakComplexGradient U u g) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    MemLp g p (volume.restrict K) := by
  obtain ⟨h, hh, _, hhmem⟩ := hu
  exact (memLp_congr_ae ((hh.unique hU hg).filter_mono
    (ae_mono (Measure.restrict_mono_set _ hKU)))).mp (hhmem K hK hKU)

end ModifiedCartan



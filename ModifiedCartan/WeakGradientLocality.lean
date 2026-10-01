import ModifiedCartan.WeakGradientUnique
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped Topology ENNReal ContDiff Manifold
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Locality of distributional weak gradients for `lem:logderivlimit`.
A finite smooth partition of a compactly supported test turns local weak
identities into the global identities, with all summands integrable. -/





theorem exists_finite_smooth_test_decomposition {ι : Type*} {V : ι → Set ℂ}
    (hV : ∀ i, IsOpen (V i)) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hcover : tsupport φ ⊆ ⋃ i, V i) :
    ∃ (S : Finset ι) (ψ : S → ℂ → ℝ), (fun z => ∑ i : S, ψ i z) = φ ∧
      ∀ i : S, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧ tsupport (ψ i) ⊆ V i := by
  classical
  obtain ⟨S, hS⟩ := hφc.elim_finite_subcover V hV hcover
  have hcover' : tsupport φ ⊆ ⋃ i : S, V i := by
    intro z hz
    obtain ⟨i, hi, hzV⟩ := mem_iUnion₂.mp (hS hz)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzV⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ)
    hφc.isClosed (fun i : S => V i) (fun i => hV i) hcover'
  refine ⟨S, fun i z => ρ i z * φ z, ?_, ?_⟩
  · funext z
    by_cases hz : z ∈ tsupport φ
    · rw [← Finset.sum_mul]
      have hone : ∑ i : S, ρ i z = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hz
      rw [hone, one_mul]
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero, Finset.sum_const_zero]
  · intro i
    refine ⟨(ρ i).contMDiff.contDiff.mul hφ, hφc.mul_left, ?_⟩
    exact tsupport_mul_subset_left.trans (hρ i)

theorem locallyIntegrableOn_of_locally {E : Type*} [NormedAddCommGroup E]
    {U : Set ℂ} {f : ℂ → E}
    (h : ∀ x ∈ U, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ LocallyIntegrableOn f V) :
    LocallyIntegrableOn f U := by
  intro x hx
  obtain ⟨V, hV, hxV, hf⟩ := h x hx
  have hxf := hf x hxV
  rw [nhdsWithin_eq_nhds.mpr (hV.mem_nhds hxV)] at hxf
  exact hxf.filter_mono nhdsWithin_le_nhds

theorem integral_test_fderiv_of_open_cover {ι : Type*} {U : Set ℂ} {V : ι → Set ℂ}
    (hV : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U) (hcover : U ⊆ ⋃ i, V i)
    {u w : ℂ → ℝ}
    (hu : ∀ K, IsCompact K → K ⊆ U → IntegrableOn u K)
    (hw : ∀ K, IsCompact K → K ⊆ U → IntegrableOn w K) (v : ℂ)
    (htest : ∀ i (ψ : ℂ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V i →
      (∫ z, u z * fderiv ℝ ψ z v) = -(∫ z, w z * ψ z))
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ z, u z * fderiv ℝ φ z v) = -(∫ z, w z * φ z) := by
  classical
  obtain ⟨S, ψ, heq, hψ⟩ := exists_finite_smooth_test_decomposition hV hφ hφc (hφU.trans hcover)
  have hψU (i : S) : tsupport (ψ i) ⊆ U := (hψ i).2.2.trans (hVU i)
  have hid (i : S) : Integrable (fun z => u z * fderiv ℝ (ψ i) z v) := by
    have h1 := (hψ i).1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
    exact integrable_mul_test_of_local_integrability hu
      ((h1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hψ i).2.1.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans (hψU i))
  have hiw (i : S) : Integrable (fun z => w z * ψ i z) :=
    integrable_mul_test_of_local_integrability hw (hψ i).1.continuous (hψ i).2.1 (hψU i)
  have hder (z : ℂ) : fderiv ℝ φ z v = ∑ i : S, fderiv ℝ (ψ i) z v := by
    rw [← heq, fderiv_fun_sum (fun i _ => (hψ i).1.differentiable (by simp) z)]
    simp only [sum_apply]
  have hleft : (∫ z, u z * fderiv ℝ φ z v) = ∑ i : S, ∫ z, u z * fderiv ℝ (ψ i) z v := by
    simp_rw [hder, Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => hid i)
  have hright : (∫ z, w z * φ z) = ∑ i : S, ∫ z, w z * ψ i z := by
    have heq' (z : ℂ) : φ z = ∑ i : S, ψ i z := (congrFun heq z).symm
    simp_rw [heq', Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => hiw i)
  rw [hleft, hright]
  simp_rw [htest _ _ (hψ _).1 (hψ _).2.1 (hψ _).2.2, Finset.sum_neg_distrib]

theorem HasWeakComplexGradient.of_locally {U : Set ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (h : ∀ x ∈ U, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ HasWeakComplexGradient V u g) :
    HasWeakComplexGradient U u g := by
  classical
  choose V hV hxV hVU hgrad using (fun x : U => h x x.2)
  have hcover : U ⊆ ⋃ x : U, V x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV _⟩
  have hu : LocallyIntegrableOn u U := locallyIntegrableOn_of_locally (fun x hx =>
    ⟨V ⟨x, hx⟩, hV _, hxV _, (locallyIntegrableOn_iff (hV _).isLocallyClosed).mpr
      (fun K hKU hK => (hgrad _).function_integrable K hK hKU)⟩)
  have hg : LocallyIntegrableOn g U := locallyIntegrableOn_of_locally (fun x hx =>
    ⟨V ⟨x, hx⟩, hV _, hxV _, (locallyIntegrableOn_iff (hV _).isLocallyClosed).mpr
      (fun K hKU hK => (hgrad _).gradient_integrable K hK hKU)⟩)
  have hui K (hK : IsCompact K) (hKU : K ⊆ U) : IntegrableOn u K :=
    hu.integrableOn_compact_subset hKU hK
  have hgi K (hK : IsCompact K) (hKU : K ⊆ U) : IntegrableOn g K :=
    hg.integrableOn_compact_subset hKU hK
  refine ⟨hui, hgi, ?_, ?_⟩
  · intro φ hφ hφc hφU
    exact integral_test_fderiv_of_open_cover hV hVU hcover hui
      (fun K hK hKU => Complex.reCLM.integrable_comp (hgi K hK hKU)) 1
      (fun i => (hgrad i).test_one) hφ hφc hφU
  · intro φ hφ hφc hφU
    exact integral_test_fderiv_of_open_cover hV hVU hcover hui
      (fun K hK hKU => (-Complex.imCLM).integrable_comp (hgi K hK hKU)) Complex.I
      (fun i => (hgrad i).test_I) hφ hφc hφU




end ModifiedCartan



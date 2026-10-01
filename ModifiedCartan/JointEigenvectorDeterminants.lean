import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Complex.Basic

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- A map from a finite dimensional space has a nonzero kernel exactly when
    all its square composites have zero determinant. -/
theorem ker_ne_bot_iff_forall_comp_det_eq_zero {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    LinearMap.ker f ≠ ⊥ ↔ ∀ g : W →ₗ[K] V, LinearMap.det (g.comp f) = 0 := by
  constructor
  · intro hf g
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hf
    have hgv : v ∈ LinearMap.ker (g.comp f) := by
      change g (f v) = 0
      rw [LinearMap.mem_ker.mp hv, map_zero]
    intro he
    rw [he] at hgv
    exact hv0 hgv
  · intro h hf
    obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hf
    have he := h g
    rw [hg, LinearMap.det_id] at he
    exact one_ne_zero he

def jointEigenvectorEquation {K ι V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (T : ι → Module.End K V) (χ : ι → K) :
    V →ₗ[K] (ι → V) :=
  LinearMap.pi (fun i => T i - χ i • LinearMap.id)

theorem jointEigenvectorEquation_apply {K ι V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (T : ι → Module.End K V) (χ : ι → K)
    (v : V) (i : ι) : jointEigenvectorEquation T χ v i = T i v - χ i • v := rfl

/-- Common eigenvectors are characterized by polynomial determinant tests.
    Auxiliary to the inverse part of manuscript `lem:KP-correspondence`. -/
theorem commonEigenvector_iff_forall_det_eq_zero {K ι V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : ι → Module.End K V) (χ : ι → K) :
    (∃ v : V, v ≠ 0 ∧ ∀ i, T i v = χ i • v) ↔
      ∀ g : (ι → V) →ₗ[K] V, LinearMap.det (g.comp (jointEigenvectorEquation T χ)) = 0 := by
  rw [← ker_ne_bot_iff_forall_comp_det_eq_zero]
  constructor
  · rintro ⟨v, hv0, hv⟩ he
    have hm : v ∈ LinearMap.ker (jointEigenvectorEquation T χ) := by
      apply LinearMap.mem_ker.mpr
      funext i
      exact sub_eq_zero.mpr (hv i)
    rw [he] at hm
    exact hv0 hm
  · intro he
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
    refine ⟨v, hv0, ?_⟩
    intro i
    have hi := congrFun (LinearMap.mem_ker.mp hv) i
    exact sub_eq_zero.mp hi

end
end ModifiedCartan

#print axioms ModifiedCartan.commonEigenvector_iff_forall_det_eq_zero

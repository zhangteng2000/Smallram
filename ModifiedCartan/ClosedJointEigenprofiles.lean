import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Maps.Proper.Basic

open scoped Classical Topology

namespace ModifiedCartan
noncomputable section

theorem commonEigenvector_exists_unit_iff {ι V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (T : ι → Module.End ℂ V) (χ : ι → ℂ) :
    (∃ v : V, v ≠ 0 ∧ ∀ i, T i v = χ i • v) ↔
      ∃ v : V, ‖v‖ = 1 ∧ ∀ i, T i v = χ i • v := by
  constructor
  · rintro ⟨v, hv, hT⟩
    let c : ℂ := (‖v‖ : ℂ)⁻¹
    refine ⟨c • v, ?_, ?_⟩
    · rw [norm_smul, show ‖c‖ = ‖v‖⁻¹ by simp only [c, norm_inv, Complex.norm_real, norm_norm]]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
    · intro i
      rw [map_smul, hT i, smul_smul, smul_smul, mul_comm]
  · rintro ⟨v, hv, hT⟩
    refine ⟨v, ?_, hT⟩
    intro hz
    rw [hz, norm_zero] at hv
    exact zero_ne_one hv

/-- Joint eigenvalue profiles have a closed graph for continuous finite
    dimensional complex operator families, even when eigenspaces collide.
    Auxiliary to the limiting part of manuscript `lem:KP-correspondence`. -/
theorem isClosed_commonEigenvector_parameters {P ι V : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (T : P → ι → Module.End ℂ V) (χ : P → ι → ℂ)
    (hT : ∀ i, Continuous (fun x : P × V => T x.1 i x.2))
    (hχ : ∀ i, Continuous (fun p : P => χ p i)) :
    IsClosed {p : P | ∃ v : V, v ≠ 0 ∧ ∀ i, T p i v = χ p i • v} := by
  let : ProperSpace V := FiniteDimensional.proper ℂ V
  let S := Metric.sphere (0 : V) 1
  let Q : Set (P × S) := {x | ∀ i, T x.1 i x.2.val = χ x.1 i • x.2.val}
  have hQ : IsClosed Q := by
    simp only [Q, Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_eq
    · exact (hT i).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    · exact ((hχ i).comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)
  have he : Prod.fst '' Q = {p : P | ∃ v : V, v ≠ 0 ∧ ∀ i, T p i v = χ p i • v} := by
    ext p
    constructor
    · rintro ⟨⟨q, v⟩, hq, rfl⟩
      apply (commonEigenvector_exists_unit_iff (T q) (χ q)).mpr
      exact ⟨v.val, mem_sphere_zero_iff_norm.mp v.property, hq⟩
    · intro hp
      obtain ⟨v, hv, hT⟩ := (commonEigenvector_exists_unit_iff (T p) (χ p)).mp hp
      exact ⟨(p, ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩), hT, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace Q hQ

end
end ModifiedCartan

#print axioms ModifiedCartan.isClosed_commonEigenvector_parameters

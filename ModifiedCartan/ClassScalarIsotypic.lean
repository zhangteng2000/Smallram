import ModifiedCartan.ClassWeightedOperator

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem classWeightedOperator_mul_projector (f : G → ℂ) (hf : IsConjugationInvariant f)
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] :
    classWeightedOperator f σ * characterProjector ρ σ =
      classScalar f ρ • characterProjector ρ σ := by
  have hle : representationIsotypicSubmodule ρ σ ≤
      LinearMap.ker (classWeightedOperator f σ - classScalar f ρ • (1 : Module.End ℂ W)) := by
    apply iSup_le
    intro L v hv
    obtain ⟨w, rfl⟩ := hv
    have hn := congrArg (fun T : V →ₗ[ℂ] W => T w) (classWeightedOperator_natural f ρ σ L)
    rw [classWeightedOperator_on_irreducible f hf ρ] at hn
    have he : classWeightedOperator f σ (L w) = classScalar f ρ • L w := by
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.one_apply,
        Representation.IntertwiningMap.toLinearMap_apply, map_smul] using hn
    change classWeightedOperator f σ (L w) - classScalar f ρ • L w = 0
    rw [he, sub_self]
  apply LinearMap.ext
  intro v
  have hk := hle (characterProjector_apply_mem_isotypic ρ σ v)
  change classWeightedOperator f σ (characterProjector ρ σ v) -
    classScalar f ρ • characterProjector ρ σ v = 0 at hk
  exact sub_eq_zero.mp hk

theorem classScalar_normalized (f : G → ℂ) (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] :
    classScalar f ρ * ((Module.finrank ℂ V : ℂ) / (Nat.card G : ℂ)) =
      (Nat.card G : ℂ)⁻¹ * ∑ g, f g⁻¹ * ρ.character g := by
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast irreducible_finrank_ne_zero ρ
  simp only [classScalar, div_eq_mul_inv]
  field_simp

theorem classWeightedOperator_regular_coefficient (f : G → ℂ) (g : G) :
    (classWeightedOperator f (Representation.leftRegular ℂ G) (MonoidAlgebra.single 1 1)).coeff g =
      f g⁻¹ := by
  simp [classWeightedOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    Representation.leftRegular, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem characterProjector_regular_coefficient (ρ : Representation ℂ G V) (g : G) :
    (characterProjector ρ (Representation.leftRegular ℂ G) (MonoidAlgebra.single 1 1)).coeff g =
      ((Module.finrank ℂ V : ℂ) / (Nat.card G : ℂ)) * ρ.character g⁻¹ := by
  change (((Module.finrank ℂ V : ℂ) / (Nat.card G : ℂ)) •
    classWeightedOperator ρ.character (Representation.leftRegular ℂ G) (MonoidAlgebra.single 1 1)).coeff g = _
  rw [MonoidAlgebra.coeff_smul_apply, classWeightedOperator_regular_coefficient, smul_eq_mul]

end
end ModifiedCartan



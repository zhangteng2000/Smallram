import ModifiedCartan.CharacterScalarAction

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W U : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem characterWeightedOperator_natural (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (τ : Representation ℂ G U)
    (f : Representation.IntertwiningMap σ τ) :
    (characterWeightedOperator ρ τ).comp f.toLinearMap =
      f.toLinearMap.comp (characterWeightedOperator ρ σ) := by
  apply LinearMap.ext
  intro v
  simp only [characterWeightedOperator, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (fun w => ρ.character g⁻¹ • w)
    (Representation.IntertwiningMap.isIntertwining σ τ f g v).symm

/-- The finite-group character projector with the general inverse convention. -/
def characterProjector (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Module.End ℂ W :=
  ((Module.finrank ℂ V : ℂ) / (Nat.card G : ℂ)) • characterWeightedOperator ρ σ

theorem characterProjector_natural (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (τ : Representation ℂ G U)
    (f : Representation.IntertwiningMap σ τ) :
    (characterProjector ρ τ).comp f.toLinearMap =
      f.toLinearMap.comp (characterProjector ρ σ) := by
  simp only [characterProjector, LinearMap.smul_comp, LinearMap.comp_smul,
    characterWeightedOperator_natural ρ σ τ f]

theorem characterProjector_on_irreducible [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ] :
    characterProjector ρ σ =
      if Nonempty (Representation.Equiv ρ σ) then (1 : Module.End ℂ W) else 0 := by
  rw [characterProjector, characterWeightedOperator_on_irreducible]
  split_ifs with h
  · rw [smul_smul]
    have hG : (Nat.card G : ℂ) ≠ 0 := by
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast (Fintype.card_ne_zero (α := G))
    have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
      exact_mod_cast irreducible_finrank_ne_zero ρ
    have hs : ((Module.finrank ℂ V : ℂ) / (Nat.card G : ℂ)) *
        ((Nat.card G : ℂ) / (Module.finrank ℂ V : ℂ)) = 1 := by
      field_simp
    rw [hs, one_smul]
  · exact smul_zero _

/-- Sum of the ranges of all equivariant maps from the fixed irreducible representation. -/
def representationIsotypicSubmodule (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) : Submodule ℂ W :=
  ⨆ f : Representation.IntertwiningMap ρ σ, LinearMap.range f.toLinearMap

theorem characterProjector_apply_intertwiner (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (f : Representation.IntertwiningMap ρ σ) (v : V) :
    characterProjector ρ σ (f v) = f v := by
  have he := congrArg (fun L : V →ₗ[ℂ] W => L v) (characterProjector_natural ρ ρ σ f)
  have hself : characterProjector ρ ρ = (1 : Module.End ℂ V) := by
    rw [characterProjector_on_irreducible]
    simp only [show Nonempty (Representation.Equiv ρ ρ) from ⟨Representation.Equiv.refl ρ⟩,
      ite_true]
  simpa only [LinearMap.comp_apply, hself, Module.End.one_apply,
    Representation.IntertwiningMap.toLinearMap_apply] using he

end
end ModifiedCartan



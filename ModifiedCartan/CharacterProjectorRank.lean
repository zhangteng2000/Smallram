import ModifiedCartan.CharacterProjectorRange
import Mathlib.LinearAlgebra.Trace

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem characterProjector_trace_formula (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    LinearMap.trace ℂ W (characterProjector ρ σ) =
      (Module.finrank ℂ V : ℂ) * ((Nat.card G : ℂ)⁻¹ *
        ∑ g : G, ρ.character g⁻¹ * σ.character g) := by
  rw [characterProjector, map_smul, characterWeightedOperator_trace, smul_eq_mul]
  calc
    _ = ((Module.finrank ℂ V : ℂ) / (Nat.card G : ℂ)) *
        ∑ g : G, ρ.character g⁻¹ * σ.character g := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      exact mul_comm _ _
    _ = _ := by rw [div_eq_mul_inv, mul_assoc]

theorem characterProjector_trace_eq_finrank_isotypic (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] :
    LinearMap.trace ℂ W (characterProjector ρ σ) =
      (Module.finrank ℂ (representationIsotypicSubmodule ρ σ) : ℂ) := by
  have hi : IsIdempotentElem (characterProjector ρ σ) := characterProjector_idempotent ρ σ
  rw [(LinearMap.IsIdempotentElem.isProj_range _ hi).trace,
    characterProjector_range_eq_isotypic]

theorem isotypic_finrank_of_character_pairing (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] (m : ℕ)
    (h : (Nat.card G : ℂ)⁻¹ * (∑ g : G, ρ.character g⁻¹ * σ.character g) = (m : ℂ)) :
    Module.finrank ℂ (representationIsotypicSubmodule ρ σ) = Module.finrank ℂ V * m := by
  have he := characterProjector_trace_formula ρ σ
  rw [characterProjector_trace_eq_finrank_isotypic, h] at he
  exact_mod_cast he

end
end ModifiedCartan



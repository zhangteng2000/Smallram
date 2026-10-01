import ModifiedCartan.CharacterOrthogonalProjection

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

theorem characterWeightedOperator_eq_scaled_projector (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] :
    characterWeightedOperator ρ σ =
      ((Nat.card G : ℂ) / (Module.finrank ℂ V : ℂ)) • characterProjector ρ σ := by
  have hG : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_ne_zero (α := G))
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast irreducible_finrank_ne_zero ρ
  rw [characterProjector, smul_smul]
  have hs : ((Nat.card G : ℂ) / (Module.finrank ℂ V : ℂ)) *
      ((Module.finrank ℂ V : ℂ) / (Nat.card G : ℂ)) = 1 := by field_simp
  rw [hs, one_smul]

theorem norm_characterWeightedOperator_apply_le (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (hσ : IsUnitaryRepresentation σ) (v : W) :
    ‖characterWeightedOperator ρ σ v‖ ≤
      ((Nat.card G : ℝ) / (Module.finrank ℂ V : ℝ)) * ‖v‖ := by
  rw [characterWeightedOperator_eq_scaled_projector ρ σ, LinearMap.smul_apply,
    norm_smul, norm_div, norm_natCast, norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_characterProjector_apply_le ρ σ hσ v) (by positivity)

/-- The convention here is linear in the operator argument, matching the paper's expectation. -/
theorem norm_characterWeightedOperator_expectation_le_card (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (hσ : IsUnitaryRepresentation σ) (v : W) (hv : ‖v‖ = 1) :
    ‖inner ℂ v (characterWeightedOperator ρ σ v)‖ ≤ (Nat.card G : ℝ) := by
  calc
    ‖inner ℂ v (characterWeightedOperator ρ σ v)‖ ≤ ‖v‖ * ‖characterWeightedOperator ρ σ v‖ :=
      norm_inner_le_norm _ _
    _ = ‖characterWeightedOperator ρ σ v‖ := by rw [hv, one_mul]
    _ ≤ (Nat.card G : ℝ) / (Module.finrank ℂ V : ℝ) := by
      simpa only [hv, mul_one] using norm_characterWeightedOperator_apply_le ρ σ hσ v
    _ ≤ (Nat.card G : ℝ) := by
      apply div_le_self (by positivity)
      have hd := irreducible_finrank_ne_zero ρ
      have hone : 1 ≤ Module.finrank ℂ V := by omega
      exact_mod_cast hone

end
end ModifiedCartan



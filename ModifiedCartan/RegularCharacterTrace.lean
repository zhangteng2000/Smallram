import ModifiedCartan.CharacterProjectorRange

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {G : Type*} [Group G] [Fintype G]

theorem leftRegular_character (g : G) :
    (Representation.leftRegular ℂ G).character g =
      if g = 1 then (Fintype.card G : ℂ) else 0 := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ)]
  by_cases hg : g = 1
  · subst g
    simp [LinearMap.toMatrix_one, Matrix.trace_one]
  · simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis,
      Representation.leftRegular, Representation.ofMulAction_single, hg,
      MonoidAlgebra.coeff_single]

theorem characterProjector_trace_regular {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    LinearMap.trace ℂ ℂ[G] (characterProjector ρ (Representation.leftRegular ℂ G)) =
      (Module.finrank ℂ V : ℂ) ^ 2 := by
  let _ := (MonoidAlgebra.basis G ℂ).finiteDimensional_of_finite
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := G)
  rw [characterProjector, map_smul, characterWeightedOperator_trace]
  simp only [leftRegular_character, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, inv_one, Representation.char_one, smul_eq_mul,
    Nat.card_eq_fintype_card]
  field_simp

end
end ModifiedCartan



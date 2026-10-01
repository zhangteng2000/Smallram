import ModifiedCartan.ClassFunctionScalarAction
import ModifiedCartan.CharacterProjectorBasic

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {G : Type*} [Group G] [Fintype G]

theorem classFunctionOperator_regular_coeff (f : G → ℂ) (g : G) :
    (classFunctionOperator f (Representation.leftRegular ℂ G)
      (MonoidAlgebra.single 1 1)).coeff g = f g⁻¹ := by
  simp [classFunctionOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    Representation.leftRegular, Representation.ofMulAction_single,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
    MonoidAlgebra.coeff_smul_apply, Finsupp.single_apply]

theorem characterProjector_regular_coeff {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    (characterProjector ρ (Representation.leftRegular ℂ G)
      (MonoidAlgebra.single 1 1)).coeff g =
      ((Module.finrank ℂ V : ℂ) / (Nat.card G : ℂ)) * ρ.character g⁻¹ := by
  rw [characterProjector, LinearMap.smul_apply, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  change _ * (classFunctionOperator ρ.character (Representation.leftRegular ℂ G)
    (MonoidAlgebra.single 1 1)).coeff g = _
  rw [classFunctionOperator_regular_coeff]

def classFunctionFourierCoefficient {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : G → ℂ) (ρ : Representation ℂ G V) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * ρ.character g⁻¹

theorem classFunctionScalar_mul_dimension {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : G → ℂ) (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] :
    classFunctionScalar f ρ * ((Module.finrank ℂ V : ℂ) / (Nat.card G : ℂ)) =
      classFunctionFourierCoefficient f ρ := by
  have hs : (∑ g : G, f g⁻¹ * ρ.character g) = ∑ g : G, f g * ρ.character g⁻¹ := by
    simpa only [Equiv.inv_apply, inv_inv] using
      Equiv.sum_comp (Equiv.inv G) (fun g => f g * ρ.character g⁻¹)
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast irreducible_finrank_ne_zero ρ
  have hG : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero (α := G)
  rw [classFunctionScalar, classFunctionFourierCoefficient, hs]
  field_simp

end
end ModifiedCartan


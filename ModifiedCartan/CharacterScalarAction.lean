import ModifiedCartan.CentralCharacterOperator
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem characterWeightedOperator_trace (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) :
    LinearMap.trace ℂ W (characterWeightedOperator ρ σ) =
      ∑ g : G, σ.character g * ρ.character g⁻¹ := by
  simp [characterWeightedOperator, Representation.character, map_sum, map_smul,
    smul_eq_mul, mul_comm]

theorem exists_scalar_characterWeightedOperator (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible σ] :
    ∃ c : ℂ, characterWeightedOperator ρ σ = c • (1 : Module.End ℂ W) := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := σ)).surjective (characterWeightedIntertwiner ρ σ)
  refine ⟨c, ?_⟩
  exact (congrArg (fun F : Representation.IntertwiningMap σ σ => F.toLinearMap) hc).symm

theorem irreducible_finrank_ne_zero (σ : Representation ℂ G W)
    [Representation.IsIrreducible σ] : Module.finrank ℂ W ≠ 0 := by
  letI : Nontrivial σ.asModule := IsSimpleModule.nontrivial ℂ[G] σ.asModule
  letI : Nontrivial W := inferInstanceAs (Nontrivial σ.asModule)
  exact ((Module.finrank_pos_iff_of_free ℂ W).mpr inferInstance).ne'

/-- Exact scalar of the character sum on every irreducible representation. -/
theorem characterWeightedOperator_on_irreducible (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    [Representation.IsIrreducible σ] :
    characterWeightedOperator ρ σ =
      if Nonempty (Representation.Equiv ρ σ) then
        ((Nat.card G : ℂ) / (Module.finrank ℂ V : ℂ)) • (1 : Module.End ℂ W)
      else 0 := by
  have hG : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_ne_zero (α := G))
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hG
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast irreducible_finrank_ne_zero σ
  obtain ⟨c, hc⟩ := exists_scalar_characterWeightedOperator ρ σ
  have ho := Representation.char_orthonormal σ ρ
  rw [← characterWeightedOperator_trace ρ σ, hc, map_smul, LinearMap.trace_one,
    smul_eq_mul] at ho
  rw [hc]
  split_ifs with he
  · rw [if_pos he] at ho
    have hdim := (Classical.choice he).toLinearEquiv.finrank_eq
    have hcd : c * (Module.finrank ℂ W : ℂ) = (Nat.card G : ℂ) := by
      field_simp [hG] at ho
      exact ho
    have hcval : c = (Nat.card G : ℂ) / (Module.finrank ℂ W : ℂ) := (eq_div_iff hd).mpr hcd
    rw [hcval, hdim]
  · rw [if_neg he] at ho
    have hz : c * (Module.finrank ℂ W : ℂ) = 0 := by
      field_simp [hG] at ho
      simpa only [mul_zero] using ho
    rw [(mul_eq_zero.mp hz).resolve_right hd, zero_smul]

end
end ModifiedCartan



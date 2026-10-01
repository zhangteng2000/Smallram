import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Tactic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Character-weighted operator, with the inverse convention for a general finite group. -/
def characterWeightedOperator (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Module.End ℂ W := ∑ g : G, ρ.character g⁻¹ • σ g

theorem characterWeightedOperator_commutes (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (h : G) :
    characterWeightedOperator ρ σ * σ h = σ h * characterWeightedOperator ρ σ := by
  let e : G ≃ G :=
    { toFun := fun g => h * g * h⁻¹
      invFun := fun g => h⁻¹ * g * h
      left_inv := by intro g; group
      right_inv := by intro g; group }
  calc
    characterWeightedOperator ρ σ * σ h =
        ∑ g : G, ρ.character g⁻¹ • σ (g * h) := by
      simp only [characterWeightedOperator, Finset.sum_mul, smul_mul_assoc, map_mul]
    _ = ∑ g : G, ρ.character (h * g * h⁻¹)⁻¹ • σ ((h * g * h⁻¹) * h) :=
      (e.sum_comp (fun g => ρ.character g⁻¹ • σ (g * h))).symm
    _ = ∑ g : G, ρ.character g⁻¹ • σ (h * g) := by
      apply Finset.sum_congr rfl
      intro g _
      have hinv : (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ := by group
      have hprod : (h * g * h⁻¹) * h = h * g := by group
      rw [hinv, hprod, Representation.char_conj]
    _ = σ h * characterWeightedOperator ρ σ := by
      simp only [characterWeightedOperator, Finset.mul_sum, mul_smul_comm, map_mul]

def characterWeightedIntertwiner (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Representation.IntertwiningMap σ σ where
  toLinearMap := characterWeightedOperator ρ σ
  isIntertwining' h := characterWeightedOperator_commutes ρ σ h

end
end ModifiedCartan



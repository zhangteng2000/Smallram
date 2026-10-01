import ModifiedCartan.CharacterScalarAction

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def IsConjugacyInvariant (f : G → ℂ) : Prop := ∀ g h, f (h * g * h⁻¹) = f g

def classFunctionOperator (f : G → ℂ) (ρ : Representation ℂ G V) : Module.End ℂ V :=
  ∑ g : G, f g⁻¹ • ρ g

theorem classFunctionOperator_commutes (f : G → ℂ) (hf : IsConjugacyInvariant f)
    (ρ : Representation ℂ G V) (h : G) :
    classFunctionOperator f ρ * ρ h = ρ h * classFunctionOperator f ρ := by
  let e : G ≃ G :=
    { toFun := fun g => h * g * h⁻¹
      invFun := fun g => h⁻¹ * g * h
      left_inv := by intro g; group
      right_inv := by intro g; group }
  calc
    _ = ∑ g : G, f g⁻¹ • ρ (g * h) := by
      simp only [classFunctionOperator, Finset.sum_mul, smul_mul_assoc, map_mul]
    _ = ∑ g : G, f (h * g * h⁻¹)⁻¹ • ρ ((h * g * h⁻¹) * h) :=
      (e.sum_comp (fun g => f g⁻¹ • ρ (g * h))).symm
    _ = ∑ g : G, f g⁻¹ • ρ (h * g) := by
      apply Finset.sum_congr rfl
      intro g hg
      have hinv : (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ := by group
      have hprod : (h * g * h⁻¹) * h = h * g := by group
      rw [hinv, hprod, hf]
    _ = _ := by
      simp only [classFunctionOperator, Finset.mul_sum, mul_smul_comm, map_mul]

def classFunctionIntertwiner (f : G → ℂ) (hf : IsConjugacyInvariant f)
    (ρ : Representation ℂ G V) : Representation.IntertwiningMap ρ ρ where
  toLinearMap := classFunctionOperator f ρ
  isIntertwining' h := classFunctionOperator_commutes f hf ρ h

theorem classFunctionOperator_natural (f : G → ℂ) (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (F : Representation.IntertwiningMap ρ σ) :
    (classFunctionOperator f σ).comp F.toLinearMap =
      F.toLinearMap.comp (classFunctionOperator f ρ) := by
  apply LinearMap.ext
  intro v
  simp only [classFunctionOperator, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro g hg
  exact congrArg (fun w => f g⁻¹ • w)
    (Representation.IntertwiningMap.isIntertwining ρ σ F g v).symm

end
end ModifiedCartan


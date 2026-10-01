import ModifiedCartan.CharacterProjectorRange

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def IsConjugationInvariant (f : G → ℂ) : Prop :=
  ∀ g h, f (h * g * h⁻¹) = f g

def classWeightedOperator (f : G → ℂ) (ρ : Representation ℂ G V) : Module.End ℂ V :=
  ∑ g, f g⁻¹ • ρ g

theorem classWeightedOperator_natural (f : G → ℂ) (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (L : Representation.IntertwiningMap ρ σ) :
    (classWeightedOperator f σ).comp L.toLinearMap =
      L.toLinearMap.comp (classWeightedOperator f ρ) := by
  apply LinearMap.ext
  intro v
  simp only [classWeightedOperator, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (fun w => f g⁻¹ • w)
    (Representation.IntertwiningMap.isIntertwining ρ σ L g v).symm

theorem classWeightedOperator_commutes (f : G → ℂ) (hf : IsConjugationInvariant f)
    (ρ : Representation ℂ G V) (h : G) :
    classWeightedOperator f ρ * ρ h = ρ h * classWeightedOperator f ρ := by
  let e : G ≃ G :=
    { toFun := fun g => h * g * h⁻¹
      invFun := fun g => h⁻¹ * g * h
      left_inv := by intro g; group
      right_inv := by intro g; group }
  calc
    classWeightedOperator f ρ * ρ h = ∑ g, f g⁻¹ • ρ (g * h) := by
      simp only [classWeightedOperator, Finset.sum_mul, smul_mul_assoc, map_mul]
    _ = ∑ g, f (h * g * h⁻¹)⁻¹ • ρ ((h * g * h⁻¹) * h) :=
      (e.sum_comp (fun g => f g⁻¹ • ρ (g * h))).symm
    _ = ∑ g, f g⁻¹ • ρ (h * g) := by
      apply Finset.sum_congr rfl
      intro g _
      have hi : (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ := by group
      have hm : (h * g * h⁻¹) * h = h * g := by group
      rw [hi, hm, hf]
    _ = ρ h * classWeightedOperator f ρ := by
      simp only [classWeightedOperator, Finset.mul_sum, mul_smul_comm, map_mul]

def classWeightedIntertwiner (f : G → ℂ) (hf : IsConjugationInvariant f)
    (ρ : Representation ℂ G V) : Representation.IntertwiningMap ρ ρ where
  toLinearMap := classWeightedOperator f ρ
  isIntertwining' h := classWeightedOperator_commutes f hf ρ h

theorem classWeightedOperator_trace [FiniteDimensional ℂ V]
    (f : G → ℂ) (ρ : Representation ℂ G V) :
    LinearMap.trace ℂ V (classWeightedOperator f ρ) = ∑ g, f g⁻¹ * ρ.character g := by
  simp [classWeightedOperator, Representation.character, map_sum, map_smul, smul_eq_mul]

def classScalar [FiniteDimensional ℂ V] (f : G → ℂ) (ρ : Representation ℂ G V) : ℂ :=
  (∑ g, f g⁻¹ * ρ.character g) / (Module.finrank ℂ V : ℂ)

theorem classWeightedOperator_on_irreducible [FiniteDimensional ℂ V]
    (f : G → ℂ) (hf : IsConjugationInvariant f) (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] :
    classWeightedOperator f ρ = classScalar f ρ • (1 : Module.End ℂ V) := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (classWeightedIntertwiner f hf ρ)
  have he : classWeightedOperator f ρ = c • (1 : Module.End ℂ V) :=
    (congrArg (fun L : Representation.IntertwiningMap ρ ρ => L.toLinearMap) hc).symm
  have ht := classWeightedOperator_trace f ρ
  rw [he, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast irreducible_finrank_ne_zero ρ
  have hcval : c = classScalar f ρ := (eq_div_iff hd).mpr ht
  rw [he, hcval]

end
end ModifiedCartan



import ModifiedCartan.KPJointEigenvalues

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- A common eigenspace in the sense used before manuscript
    `lem:KP-correspondence`: a nonzero subspace on which every algebra
    element acts by a scalar. No maximality condition is imposed. -/
def IsCommonEigenspace {R V : Type*} [Semiring R] [Algebra ℂ R]
    [AddCommGroup V] [Module ℂ V] (ρ : R →ₐ[ℂ] Module.End ℂ V)
    (B : Subalgebra ℂ R) (E : Submodule ℂ V) : Prop :=
  E ≠ ⊥ ∧ ∀ x ∈ B, ∃ c : ℂ, ∀ v ∈ E, ρ x v = c • v

theorem isCommonEigenspace_adjoin_iff {R V : Type*} [Semiring R] [Algebra ℂ R]
    [AddCommGroup V] [Module ℂ V] (ρ : R →ₐ[ℂ] Module.End ℂ V)
    (s : Set R) (E : Submodule ℂ V) :
    IsCommonEigenspace ρ (Algebra.adjoin ℂ s) E ↔
      E ≠ ⊥ ∧ ∀ x ∈ s, ∃ c : ℂ, ∀ v ∈ E, ρ x v = c • v := by
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨hne, fun x hx => h x (Algebra.subset_adjoin hx)⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, scalar_action_of_mem_adjoin ρ E s h⟩

theorem kp_isCommonEigenspace_iff {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (E : Submodule ℂ (YoungSpechtModule τ)) :
    IsCommonEigenspace (spechtRepresentationOn τ hτ).asAlgebraHom
      (kpGeneratedAlgebra z) E ↔
      E ≠ ⊥ ∧ ∃ χ : YoungDiagram → ℂ, E ≤ kpJointEigenspace τ hτ z χ := by
  rw [kpGeneratedAlgebra, isCommonEigenspace_adjoin_iff]
  constructor
  · rintro ⟨hne, h⟩
    have hg : ∀ μ : YoungDiagram, ∃ c : ℂ, ∀ v ∈ E,
        (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z 0) v = c • v :=
      fun μ => h _ ⟨μ, rfl⟩
    choose χ hχ using hg
    exact ⟨hne, χ, fun v hv => (mem_kpJointEigenspace_iff τ hτ z χ v).mpr
      (fun μ => hχ μ v hv)⟩
  · rintro ⟨hne, χ, hχ⟩
    refine ⟨hne, ?_⟩
    rintro _ ⟨μ, rfl⟩
    exact ⟨χ μ, fun v hv => (mem_kpJointEigenspace_iff τ hτ z χ v).mp (hχ hv) μ⟩

theorem kpJointEigenspace_isCommonEigenspace {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    IsCommonEigenspace (spechtRepresentationOn τ hτ).asAlgebraHom
      (kpGeneratedAlgebra z) (kpJointEigenspace τ hτ z χ) :=
  (kp_isCommonEigenspace_iff τ hτ z _).mpr ⟨hne, χ, le_rfl⟩

end
end ModifiedCartan

#print axioms ModifiedCartan.kp_isCommonEigenspace_iff
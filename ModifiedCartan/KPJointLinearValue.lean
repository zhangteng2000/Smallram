import ModifiedCartan.FiniteGroupLinearCoefficients
import ModifiedCartan.KPJointCharacter

open scoped Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- An actual joint eigenspace supplies a linear functional on the full group
    algebra whose values on beta products are the products of the eigenvalues.
    The functional is constructed from the already proved algebra character. -/
theorem exists_kpJointLinearValue {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ h z χ ≠ ⊥) :
    ∃ L : ℂ[Equiv.Perm A] →ₗ[ℂ] ℂ, ∀ μ ν : YoungDiagram,
      L (kpBeta μ z 0 * kpBeta ν z 0) = χ μ * χ ν := by
  obtain ⟨φ, hφ, _⟩ := exists_kpJointCharacter τ h z χ hne
  obtain ⟨L, hL⟩ := subalgebraCharacter_exists_linear_extension (kpGeneratedAlgebra z) φ
  refine ⟨L, fun μ ν => ?_⟩
  have he := hL ((⟨kpBeta μ z 0, kpBeta_zero_mem_generated μ z⟩ : kpGeneratedAlgebra z) *
    ⟨kpBeta ν z 0, kpBeta_zero_mem_generated ν z⟩)
  rw [map_mul, hφ, hφ] at he
  exact he

end
end ModifiedCartan

#print axioms ModifiedCartan.exists_kpJointLinearValue

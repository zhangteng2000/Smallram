import ModifiedCartan.JointEigenvectorDeterminants
import ModifiedCartan.KPJointProfileClosed
import ModifiedCartan.KPSpechtSupport
import ModifiedCartan.SchubertCoordinatePolynomials

open scoped Classical

namespace ModifiedCartan
noncomputable section

def finiteKPJointEquation {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ) :
    YoungSpechtModule τ →ₗ[ℂ] (Subpartition τ → YoungSpechtModule τ) :=
  jointEigenvectorEquation
    (fun μ : Subpartition τ => (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ.val z 0))
    (fun μ : Subpartition τ => χ μ.val)

theorem kpJointEigenspace_ne_bot_iff_finite_commonEigenvector {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ) (hχ : ∀ μ, ¬ μ ≤ τ → χ μ = 0) :
    kpJointEigenspace τ hτ z χ ≠ ⊥ ↔
      ∃ v : YoungSpechtModule τ, v ≠ 0 ∧ ∀ μ : Subpartition τ,
        (spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ.val z 0) v = χ μ.val • v := by
  rw [kpJointEigenspace_ne_bot_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, fun μ => h μ.val⟩
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    intro μ
    by_cases hμ : μ ≤ τ
    · exact h ⟨μ, hμ⟩
    · rw [specht_kpBeta_eq_zero_of_not_le μ τ hτ hμ, hχ μ hμ,
        LinearMap.zero_apply, zero_smul]

/-- A finite determinant criterion for the actual KP joint eigenspace.
    The support hypothesis is precisely the already proved Schubert support,
    and is discharged for the chart below. Auxiliary to `lem:KP-correspondence`. -/
theorem kpJointEigenspace_ne_bot_iff_finite_det {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ) (hχ : ∀ μ, ¬ μ ≤ τ → χ μ = 0) :
    kpJointEigenspace τ hτ z χ ≠ ⊥ ↔
      ∀ g : (Subpartition τ → YoungSpechtModule τ) →ₗ[ℂ] YoungSpechtModule τ,
        LinearMap.det (g.comp (finiteKPJointEquation τ hτ z χ)) = 0 := by
  rw [kpJointEigenspace_ne_bot_iff_finite_commonEigenvector τ hτ z χ hχ]
  exact commonEigenvector_iff_forall_det_eq_zero _ _

theorem schubertCoordinatePolynomial_eval_eq_zero_of_not_le {n : ℕ}
    (τ μ : YoungDiagram) (hτ : PartitionFits n τ) (x : SchubertChartSlot n τ → ℂ)
    (hμ : ¬ μ ≤ τ) : MvPolynomial.eval x (schubertCoordinatePolynomial τ μ) = 0 := by
  rw [schubertCoordinatePolynomial_eval τ μ hτ x]
  exact normalizedPartitionMinor_eq_zero_of_not_le (schubertChartPolynomial τ x)
    (schubertChartPolynomial_natDegree_le τ x) μ hμ 0

/-- Finite determinant equations are equivalent to a nonzero actual joint
    eigenspace for every point of the actual Schubert chart. -/
theorem kpJointEigenspace_chart_ne_bot_iff_finite_det {n : ℕ} {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (hf : PartitionFits n τ)
    (z : A → ℂ) (x : SchubertChartSlot n τ → ℂ) :
    kpJointEigenspace τ hτ z
      (fun μ => MvPolynomial.eval x (schubertCoordinatePolynomial τ μ)) ≠ ⊥ ↔
      ∀ g : (Subpartition τ → YoungSpechtModule τ) →ₗ[ℂ] YoungSpechtModule τ,
        LinearMap.det (g.comp (finiteKPJointEquation τ hτ z
          (fun μ => MvPolynomial.eval x (schubertCoordinatePolynomial τ μ)))) = 0 :=
  kpJointEigenspace_ne_bot_iff_finite_det τ hτ z _
    (fun μ hμ => schubertCoordinatePolynomial_eval_eq_zero_of_not_le τ μ hf x hμ)

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointEigenspace_chart_ne_bot_iff_finite_det

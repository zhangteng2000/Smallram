import ModifiedCartan.SubgroupFiniteSumCoefficient
import ModifiedCartan.SupportedRestrictionEquivalence
import ModifiedCartan.FiniteFrobeniusPolynomials

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

def supportedCycleSum {A : Type*} [Fintype A] (B : Type*) [Fintype B] (X : Finset A) :
    MonoidAlgebra (MvPolynomial B ℂ) (Equiv.Perm A) :=
  ∑ π : supportedPermutationSubgroup X,
    MonoidAlgebra.single π.val
      (finiteCyclePolynomial B (supportedPermutationRestriction X π.val π.property))

/-- The finite character-transform coefficients are exactly the existing
KP alpha operators on each support. LaTeX `eq:KP-operators`. This theorem
does not yet identify those transforms with Schur determinants. -/
theorem supportedCycleSum_frobenius_coeff {A B : Type*} [Fintype A] [Fintype B]
    (X : Finset A) (θ : Equiv.Perm A) :
    (supportedCycleSum B X).coeff θ =
      ∑ μ : SizedYoungDiagram (Fintype.card X),
        MvPolynomial.C ((kpAlpha μ.val X).coeff θ) * finiteFrobeniusPolynomial B μ.val := by
  rw [supportedCycleSum, subgroup_finite_sum_coefficient]
  by_cases hθ : θ ∈ supportedPermutationSubgroup X
  · rw [dite_eq_left hθ, finiteCyclePolynomial_frobenius]
    apply Finset.sum_congr rfl
    intro μ hμ
    rw [kpAlpha_coefficient μ.val X ((Fintype.card_coe X).symm.trans μ.property.symm) θ,
      dite_eq_left hθ, supportedPermutationRestriction_eq_symm]
  · rw [dite_eq_right hθ]
    symm
    apply Finset.sum_eq_zero
    intro μ hμ
    rw [kpAlpha_coefficient μ.val X ((Fintype.card_coe X).symm.trans μ.property.symm) θ,
      dite_eq_right hθ, map_zero, zero_mul]

end
end ModifiedCartan


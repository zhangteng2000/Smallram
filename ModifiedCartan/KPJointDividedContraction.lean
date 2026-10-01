import ModifiedCartan.PartitionAlternatingPolynomial
import ModifiedCartan.MvDividedPowerNormalization

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def finitePartitionDividedPolynomial (d N : ℕ) (χ : YoungDiagram → ℂ) :
    MvPolynomial (Fin d) ℂ :=
  mvDividedPowerNormalize (Fin d) (finitePartitionAlternatingPolynomial d N χ)

theorem kpJointDividedPolynomial_ne_zero {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    finitePartitionDividedPolynomial (Fintype.card A) (Fintype.card A) χ ≠ 0 :=
  mvDividedPowerNormalize_ne_zero _ (kpJointAlternatingPolynomial_ne_zero τ hτ z χ hne)

/-- The actual joint alternating polynomial in divided powers has the exact
    factorial-weighted contraction needed for the differential operator.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem kpJointDividedPolynomial_first_contraction {A : Type*} [Fintype A]
    {m : ℕ} (hm : Fintype.card A = m + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    (∑ k ∈ Finset.range (Fintype.card A + 1),
      MvPolynomial.C (((-1 : ℂ) ^ k * χ (columnPartition k)) *
        ((m + 1 - k).factorial : ℂ)) *
        (MvPolynomial.finSuccEquiv ℂ m
          (finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ)).coeff
            (m + 1 - k)) = 0 := by
  have h := congrArg (mvDividedPowerNormalize (Fin m))
    (kpJointAlternatingPolynomial_first_contraction hm τ hτ z χ hne)
  simpa only [map_sum, map_zero, mvDividedPowerNormalize_C_mul,
    mvDividedPowerNormalize_first_coeff, map_mul, mul_assoc,
    finitePartitionDividedPolynomial] using h

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointDividedPolynomial_first_contraction

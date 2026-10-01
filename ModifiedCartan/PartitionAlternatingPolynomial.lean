import ModifiedCartan.KPJointAlternantContraction
import ModifiedCartan.KPJointWronskian

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The finite alternating polynomial with the prescribed partition coefficients.
    `d` is its number of variables and `N` bounds the partition square. -/
def finitePartitionAlternatingPolynomial (d N : ℕ) (χ : YoungDiagram → ℂ) :
    MvPolynomial (Fin d) ℂ :=
  ∑ μ : Subpartition (partitionSquare N), MvPolynomial.C (χ μ.val) *
    finiteAlternant (partitionAlternantExponent d μ.val)

theorem finitePartitionAlternatingPolynomial_coeff {d N : ℕ} (hd : N ≤ d)
    (χ : YoungDiagram → ℂ) (μ : Subpartition (partitionSquare N)) :
    MvPolynomial.coeff (partitionFiniteDegree d μ.val + finiteStaircaseDegree d)
      (finitePartitionAlternatingPolynomial d N χ) = χ μ.val := by
  simp only [finitePartitionAlternatingPolynomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul]
  have hc (ν : Subpartition (partitionSquare N)) := finiteAlternant_partition_coeff
    ν.val μ.val ((subpartitionSquare_height_le ν).trans hd) ((subpartitionSquare_height_le μ).trans hd)
  simp_rw [hc]
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν hν hne
    have hv : ν.val ≠ μ.val := fun he => hne (Subtype.ext he)
    simp [hv]
  · simp

theorem finitePartitionAlternatingPolynomial_ne_zero {d N : ℕ} (hd : N ≤ d)
    (χ : YoungDiagram → ℂ) (μ : Subpartition (partitionSquare N)) (hχ : χ μ.val ≠ 0) :
    finitePartitionAlternatingPolynomial d N χ ≠ 0 := by
  intro hz
  have he := finitePartitionAlternatingPolynomial_coeff hd χ μ
  rw [hz, MvPolynomial.coeff_zero] at he
  exact hχ he.symm

theorem finSuccEquiv_constant (m : ℕ) (c : ℂ) :
    MvPolynomial.finSuccEquiv ℂ m (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp [MvPolynomial.finSuccEquiv_apply]

theorem finitePartitionAlternatingPolynomial_first_coeff (m N : ℕ)
    (χ : YoungDiagram → ℂ) (j : ℕ) :
    (MvPolynomial.finSuccEquiv ℂ m (finitePartitionAlternatingPolynomial (m + 1) N χ)).coeff j =
      ∑ μ : Subpartition (partitionSquare N), MvPolynomial.C (χ μ.val) *
        (MvPolynomial.finSuccEquiv ℂ m
          (finiteAlternant (partitionAlternantExponent (m + 1) μ.val))).coeff j := by
  simp only [finitePartitionAlternatingPolynomial, map_sum, map_mul,
    finSuccEquiv_constant, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]

/-- The assembled alternating polynomial is nonzero for every actual nonzero
    joint eigenspace. Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem kpJointAlternatingPolynomial_ne_zero {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    finitePartitionAlternatingPolynomial (Fintype.card A) (Fintype.card A) χ ≠ 0 := by
  have hs : τ ≤ partitionSquare (Fintype.card A) := by
    simpa only [hτ] using partition_le_square τ
  exact finitePartitionAlternatingPolynomial_ne_zero le_rfl χ ⟨τ, hs⟩
    (kpJointEigenvalue_top_ne_zero τ hτ z χ hne)

/-- The single-column equation packaged as a zero contraction of the actual
    nonzero alternating polynomial. Auxiliary to `lem:KP-correspondence`. -/
theorem kpJointAlternatingPolynomial_first_contraction {A : Type*} [Fintype A]
    {m : ℕ} (hm : Fintype.card A = m + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    (∑ k ∈ Finset.range (Fintype.card A + 1),
      MvPolynomial.C ((-1 : ℂ) ^ k * χ (columnPartition k)) *
        (MvPolynomial.finSuccEquiv ℂ m
          (finitePartitionAlternatingPolynomial (m + 1) (Fintype.card A) χ)).coeff
            (m + 1 - k)) = 0 := by
  simp only [finitePartitionAlternatingPolynomial_first_coeff, Finset.mul_sum]
  convert kpJointAlternant_contraction hm τ hτ z χ hne using 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro μ hμ
  simp only [map_mul]
  ring

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointAlternatingPolynomial_ne_zero
#print axioms ModifiedCartan.kpJointAlternatingPolynomial_first_contraction

import ModifiedCartan.KPJointBernsteinResidue

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem subpartitionSquare_height_le {n : ℕ} (μ : Subpartition (partitionSquare n)) :
    μ.val.colLen 0 ≤ n := by
  by_contra hn
  have hm : (n, 0) ∈ μ.val := YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge hn)
  have hs := μ.property hm
  have hh := Finset.mem_range.mp (Finset.mem_product.mp hs).1
  omega

/-- The single-variable contraction of the actual alternating coefficient
    polynomial is zero on every nonzero joint eigenspace. This is the finite
    single-column relation needed for manuscript `lem:KP-correspondence`. -/
theorem kpJointAlternant_contraction {A : Type*} [Fintype A]
    {m : ℕ} (hm : Fintype.card A = m + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    (∑ k ∈ Finset.range (Fintype.card A + 1),
      ∑ μ : Subpartition (partitionSquare (Fintype.card A)),
        MvPolynomial.C ((-1 : ℂ) ^ k * (χ (columnPartition k) * χ μ.val)) *
          (MvPolynomial.finSuccEquiv ℂ m
            (finiteAlternant (partitionAlternantExponent (m + 1) μ.val))).coeff
              (m + 1 - k)) = 0 := by
  have h := congrArg (fun P : MvPolynomial (Fin m) ℂ => finiteVandermondeAlternant m * P)
    (kpJointFrobeniusBernstein_residue (B := Fin m) τ hτ z χ hne)
  rw [mul_zero, Finset.mul_sum] at h
  simp only [Finset.mul_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro μ hμ
  have hμ' : μ.val.colLen 0 ≤ m + 1 := by
    simpa only [hm] using subpartitionSquare_height_le μ
  have hk' : k ≤ m + 1 := by
    have hr := Finset.mem_range.mp hk
    omega
  rw [← finiteFrobeniusBernsteinResidue_mul_vandermonde μ.val hμ' hk']
  exact mul_left_comm _ _ _

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointAlternant_contraction

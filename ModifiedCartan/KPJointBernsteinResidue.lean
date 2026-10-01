import ModifiedCartan.KPJointLinearValue
import ModifiedCartan.KPFrobeniusBernsteinResidue

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- Every actual nonzero joint eigenspace satisfies the finite scalar
    Bernstein relation. No distinctness condition is placed on the parameters.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem kpJointFrobeniusBernstein_residue {A B : Type*}
    [Fintype A] [Fintype B]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    (∑ k ∈ Finset.range (Fintype.card A + 1),
      ∑ μ : Subpartition (partitionSquare (Fintype.card A)),
        MvPolynomial.C ((-1 : ℂ) ^ k * (χ (columnPartition k) * χ μ.val)) *
          finiteFrobeniusBernsteinResidue B μ.val k) = 0 := by
  obtain ⟨L, hL⟩ := exists_kpJointLinearValue τ hτ z χ hne
  let I := Fin (Fintype.card A + 1) × Subpartition (partitionSquare (Fintype.card A))
  let c (i : I) := kpBeta (columnPartition i.1.val) z 0 * kpBeta i.2.val z 0
  let P (i : I) := MvPolynomial.C ((-1 : ℂ) ^ i.1.val) *
    finiteFrobeniusBernsteinResidue B i.2.val i.1.val
  have hc (g : Equiv.Perm A) : (∑ i : I, MvPolynomial.C ((c i).coeff g) * P i) = 0 := by
    dsimp [I, c, P]
    rw [Fintype.sum_prod_type]
    dsimp only
    erw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      ∑ μ : Subpartition (partitionSquare (Fintype.card A)),
        MvPolynomial.C ((kpBeta (columnPartition k) z 0 * kpBeta μ.val z 0).coeff g) *
          (MvPolynomial.C ((-1 : ℂ) ^ k) * finiteFrobeniusBernsteinResidue B μ.val k))
      (Fintype.card A + 1)]
    convert kpFrobeniusBernstein_residue (B := B) z g using 1
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro μ hμ
    simp only [map_mul]
    ring
  have he := finiteGroup_polynomial_relation_linear L c P hc
  dsimp [I, c, P] at he
  rw [Fintype.sum_prod_type] at he
  dsimp only at he
  erw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    ∑ μ : Subpartition (partitionSquare (Fintype.card A)),
      MvPolynomial.C (L (kpBeta (columnPartition k) z 0 * kpBeta μ.val z 0)) *
        (MvPolynomial.C ((-1 : ℂ) ^ k) * finiteFrobeniusBernsteinResidue B μ.val k))
    (Fintype.card A + 1)] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [hL]
  simp only [map_mul]
  ring

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointFrobeniusBernstein_residue

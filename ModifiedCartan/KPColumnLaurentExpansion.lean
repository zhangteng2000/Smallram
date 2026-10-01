import ModifiedCartan.KPColumnLaurentIdentification

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- The whole literal first factor of KP (4.3), with every Laurent degree
    identified with the previously defined column operator.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem evaluatedColumnLaurentSeries_eq_sum {A B : Type*} [Fintype A]
    (z : A → ℂ) (θ : Equiv.Perm A) :
    evaluateSupportedMarkers (B := B) z ((supportedColumnLaurentSeries A B).coeff θ) =
      ∑ k ∈ Finset.range (Fintype.card A + 1),
        LaurentPolynomial.T (-(k : ℤ)) *
          LaurentPolynomial.C (MvPolynomial.C ((-1 : ℂ) ^ k *
            (kpBeta (columnPartition k) z 0).coeff θ)) := by
  simp only [supportedColumnLaurentSeries, kpBeta_column_supported,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_eq_single p.1.card]
  · by_cases hg : p.2.val = θ
    · simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, hg, ite_true,
        evaluateSupportedMarkers_monomial, MonoidAlgebra.coeff_smul_apply,
        smul_eq_mul, zero_add, map_mul]
      ring
    · simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, hg]
  · intro k hk hkp
    have hpk : p.1.card ≠ k := Ne.symm hkp
    simp [hpk]
  · intro hpnot
    exact False.elim (hpnot (Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _))))

end
end ModifiedCartan

#print axioms ModifiedCartan.evaluatedColumnLaurentSeries_eq_sum

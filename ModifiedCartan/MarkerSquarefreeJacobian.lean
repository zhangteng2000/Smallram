import ModifiedCartan.MarkerEmbeddingCoefficients

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem markerSquarefreeDegree_erase {A : Type*} (s : Finset A) (a : A) (ha : a ∈ s) :
    markerSquarefreeDegree s = Finsupp.single a 1 + markerSquarefreeDegree (s.erase a) := by
  ext b
  simp only [markerSquarefreeDegree_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hb : a = b
  · subst b
    simp [ha]
  · by_cases hbs : b ∈ s <;> simp [hb, Ne.symm hb, hbs]

theorem markerSquarefree_X_coeff {A R : Type*} [CommSemiring R]
    (s : Finset A) (a : A) (p : MvPolynomial A R) :
    MvPolynomial.coeff (markerSquarefreeDegree s) (MvPolynomial.X a * p) =
      if a ∈ s then MvPolynomial.coeff (markerSquarefreeDegree (s.erase a)) p else 0 := by
  by_cases ha : a ∈ s
  · rw [ite_eq_left ha, markerSquarefreeDegree_erase s a ha, MvPolynomial.coeff_X_mul]
  · rw [ite_eq_right ha, MvPolynomial.coeff_X_mul']
    have hn : a ∉ (markerSquarefreeDegree s).support := by
      simp only [Finsupp.mem_support_iff, markerSquarefreeDegree_apply, ite_eq_right ha,
        ne_eq, not_not]
    exact if_neg hn

theorem markerSquarefree_jacobian_coeff {A R : Type*} [Fintype A] [CommSemiring R]
    (s : Finset A) (v : A → R) (p : MvPolynomial A R) :
    MvPolynomial.coeff (markerSquarefreeDegree s)
        ((1 + ∑ a : A, MvPolynomial.X a * MvPolynomial.C (v a)) * p) =
      MvPolynomial.coeff (markerSquarefreeDegree s) p +
        ∑ a ∈ s, v a * MvPolynomial.coeff (markerSquarefreeDegree (s.erase a)) p := by
  rw [add_mul, one_mul, Finset.sum_mul, MvPolynomial.coeff_add, MvPolynomial.coeff_sum]
  apply congrArg (fun q => MvPolynomial.coeff (markerSquarefreeDegree s) p + q)
  calc
    _ = ∑ a : A, if a ∈ s then
        v a * MvPolynomial.coeff (markerSquarefreeDegree (s.erase a)) p else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_assoc, markerSquarefree_X_coeff, MvPolynomial.coeff_C_mul]
    _ = _ := by simp [← Finset.sum_filter]

theorem markerAffineProduct_jacobian_coeff {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (s : Finset A) (v : A → R) (h : B → R) (w : A → B → R) :
    MvPolynomial.coeff (markerSquarefreeDegree s)
        ((1 + ∑ a : A, MvPolynomial.X a * MvPolynomial.C (v a)) * markerAffineProduct h w) =
      (∑ f : s ↪ B, markerEmbeddingWeight s h w f) +
        ∑ a ∈ s, v a * ∑ f : s.erase a ↪ B, markerEmbeddingWeight (s.erase a) h w f := by
  rw [markerSquarefree_jacobian_coeff]
  simp only [markerAffineProduct_squarefree_coeff]

end
end ModifiedCartan


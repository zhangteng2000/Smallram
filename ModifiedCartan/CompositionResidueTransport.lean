import ModifiedCartan.ShiftedCompositionAlphabet

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem weightedCompositionLaurent_equiv {A B C R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [CommRing R]
    (e : A ≃ C) (ℓ : C → ℕ) (x : B → LaurentPolynomial R) :
    weightedCompositionLaurent (fun a => ℓ (e a)) x = weightedCompositionLaurent ℓ x := by
  rw [weightedCompositionLaurent_eq, weightedCompositionLaurent_eq]
  exact sum_embedding_products_equiv e
    (fun c b => normalizedGeometricLaurent (ℓ c) (LaurentPolynomial.T 1 * x b))

theorem weightedCompositionLaurent_residue {A B R : Type*} [Fintype A] [Fintype B]
    [CommRing R] [IsDomain R] [CharZero R] (ℓ : A → ℕ) (x : B → R) :
    ((∏ b : B, compositionUnusedWeight (x b)) *
      weightedCompositionLaurent ℓ (shiftedCompositionAlphabet x)).coeff (-1) = 0 := by
  have h := weightedCompositionLaurent_shifted_residue Finset.univ ℓ x
  let e : (Finset.univ : Finset A) ≃ A := Equiv.subtypeUnivEquiv (fun a => Finset.mem_univ a)
  have he := weightedCompositionLaurent_equiv e ℓ (shiftedCompositionAlphabet x)
  change weightedCompositionLaurent (fun a : (Finset.univ : Finset A) => ℓ a.val)
    (shiftedCompositionAlphabet x) = _ at he
  rw [he] at h
  exact h

theorem compositionLaurentExponent_eq {A : Type*} [Fintype A] (ℓ : A → ℕ)
    (κ : (a : A) → Fin (ℓ a)) :
    compositionLaurentExponent ℓ κ =
      ((∑ a : A, ((κ a).val + 1) : ℕ) : ℤ) -
        ((∑ a : A, ℓ a : ℕ) : ℤ) - (Fintype.card A : ℤ) := by
  simp only [compositionLaurentExponent, Finset.sum_sub_distrib, Nat.cast_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end
end ModifiedCartan


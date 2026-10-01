import ModifiedCartan.LaurentCompositionExpansion
import ModifiedCartan.EmbeddingProductTransport
import ModifiedCartan.NormalizedCompositionResidue

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

def shiftedCompositionAlphabet {B R : Type*} [CommRing R] (x : B → R) :
    Option B → LaurentPolynomial R
  | none => LaurentPolynomial.T (-1)
  | some b => LaurentPolynomial.C (x b)

theorem shiftedCompositionAlphabet_geometric {A B R : Type*} [CommRing R]
    (ℓ : A → ℕ) (x : B → R) (a : A) (b : Option B) :
    normalizedGeometricLaurent (ℓ a) (LaurentPolynomial.T 1 * shiftedCompositionAlphabet x b) =
      extraColorWeight (fun i => compositionJacobianWeight (R := R) (ℓ i))
        (fun i b => normalizedGeometricColor (ℓ i) (x b)) a b := by
  cases b with
  | none =>
    simp only [shiftedCompositionAlphabet, ← LaurentPolynomial.T_add,
      add_neg_cancel, LaurentPolynomial.T_zero, normalizedGeometricLaurent_one]
    rfl
  | some b =>
    change normalizedGeometricLaurent (ℓ a) (LaurentPolynomial.T 1 * LaurentPolynomial.C (x b)) = _
    rw [mul_comm]
    rfl

theorem weightedCompositionLaurent_shifted {A B R : Type*} [Fintype B] [CommRing R]
    (s : Finset A) (ℓ : A → ℕ) (x : B → R) :
    weightedCompositionLaurent (fun a : s => ℓ a.val) (shiftedCompositionAlphabet x) =
      normalizedCompositionSum s ℓ x + ∑ a ∈ s,
        compositionJacobianWeight (R := R) (ℓ a) * normalizedCompositionSum (s.erase a) ℓ x := by
  rw [weightedCompositionLaurent_eq]
  simp_rw [shiftedCompositionAlphabet_geometric]
  change (∑ f : s ↪ Option B, ∏ a : s,
    extraColorWeight (fun i : s => compositionJacobianWeight (R := R) (ℓ i.val))
      (fun (i : s) b => normalizedGeometricColor (ℓ i.val) (x b)) a (f a)) = _
  rw [sum_embeddings_extra_color]
  apply congrArg (fun q => normalizedCompositionSum s ℓ x + q)
  have he (a : s) := sum_embedding_products_erase s a
    (fun i b => normalizedGeometricColor (ℓ i) (x b))
  simp_rw [he]
  exact Finset.sum_coe_sort s (fun a => compositionJacobianWeight (R := R) (ℓ a) *
    normalizedCompositionSum (s.erase a) ℓ x)

/-- Exact finite-alphabet composition residue, expressed as finite sums over
positive bounded parts and injective colorings after adjoining t⁻¹. -/
theorem weightedCompositionLaurent_shifted_residue {A B R : Type*} [Fintype A] [Fintype B]
    [CommRing R] [IsDomain R] [CharZero R] (s : Finset A) (ℓ : A → ℕ) (x : B → R) :
    ((∏ b : B, compositionUnusedWeight (x b)) *
      weightedCompositionLaurent (fun a : s => ℓ a.val) (shiftedCompositionAlphabet x)).coeff (-1) = 0 := by
  rw [weightedCompositionLaurent_shifted]
  exact normalizedCompositionSum_residue s ℓ x

end
end ModifiedCartan

